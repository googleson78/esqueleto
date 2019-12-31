{-# LANGUAGE DeriveDataTypeable
           , EmptyDataDecls
           , FlexibleContexts
           , FlexibleInstances
           , FunctionalDependencies
           , MultiParamTypeClasses
           , TypeFamilies
           , UndecidableInstances
           , GADTs
 #-}
{-# LANGUAGE ConstraintKinds
           , EmptyDataDecls
           , FlexibleContexts
           , FlexibleInstances
           , FunctionalDependencies
           , GADTs
           , MultiParamTypeClasses
           , OverloadedStrings
           , UndecidableInstances
           , ScopedTypeVariables
           , InstanceSigs
           , Rank2Types
           , CPP
 #-}
-- | This is an internal module, anything exported by this module
-- may change without a major version bump.  Please use only
-- "Database.Esqueleto" if possible.
--
-- If you use this module, please report what your use case is on the issue
-- tracker so we can safely support it.
module Database.Esqueleto.Internal.Internal where

import Control.Applicative ((<|>))
import Control.Arrow ((***), first)
import Control.Exception (Exception, throw, throwIO)
import qualified Data.Maybe as Maybe
import Control.Monad (guard, ap, MonadPlus(..), void)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Resource (MonadResource, release)
import Data.Acquire (with, allocateAcquire, Acquire)
import Data.Int (Int64)
import Data.List (intersperse)
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif
import qualified Data.Monoid as Monoid
import Data.Proxy (Proxy(..))
import Database.Esqueleto.Internal.PersistentImport
import Database.Persist.Sql.Util (entityColumnNames, entityColumnCount, parseEntityValues, isIdField, hasCompositeKey)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Control.Monad.Trans.Reader as R
import qualified Control.Monad.Trans.State as S
import qualified Control.Monad.Trans.Writer as W
import qualified Data.ByteString as B
import qualified Data.Conduit as C
import qualified Data.Conduit.List as CL
import qualified Data.HashSet as HS
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Builder as TLB

import Data.Typeable (Typeable)
import Text.Blaze.Html (Html)


import Database.Esqueleto.Internal.ExprParser (TableAccess(..), parseOnExpr)

-- | (Internal) Start a 'from' query with an entity. 'from'
-- does two kinds of magic using 'fromStart', 'fromJoin' and
-- 'fromFinish':
--
--   1.  The simple but tedious magic of allowing tuples to be
--   used.
--
--   2.  The more advanced magic of creating @JOIN@s.  The
--   @JOIN@ is processed from right to left.  The rightmost
--   entity of the @JOIN@ is created with 'fromStart'.  Each
--   @JOIN@ step is then translated into a call to 'fromJoin'.
--   In the end, 'fromFinish' is called to materialize the
--   @JOIN@.
fromStart
  :: ( PersistEntity a
     , BackendCompatible SqlBackend (PersistEntityBackend a) )
  => SqlQuery (SqlExpr (PreprocessedFrom (SqlExpr (Entity a))))
fromStart = x
  where
    x = do
      let ed = entityDef (getVal x)
      ident <- newIdentFor (entityDB ed)
      let ret   = EEntity ident
          f' = FromStart ident ed
      return (EPreprocessedFrom ret f')
    getVal :: SqlQuery (SqlExpr (PreprocessedFrom (SqlExpr (Entity a)))) -> Proxy a
    getVal = const Proxy

-- | (Internal) Same as 'fromStart', but entity may be missing.
fromStartMaybe
  :: ( PersistEntity a
     , BackendCompatible SqlBackend (PersistEntityBackend a) )
  => SqlQuery (SqlExpr (PreprocessedFrom (SqlExpr (Maybe (Entity a)))))
fromStartMaybe = maybelize <$> fromStart
  where
    maybelize :: SqlExpr (PreprocessedFrom (SqlExpr (Entity a)))
              -> SqlExpr (PreprocessedFrom (SqlExpr (Maybe (Entity a))))
    maybelize (EPreprocessedFrom ret f') = EPreprocessedFrom (EMaybe ret) f'

-- | (Internal) Do a @JOIN@.
fromJoin
  :: IsJoinKind join
  => SqlExpr (PreprocessedFrom a)
  -> SqlExpr (PreprocessedFrom b)
  -> SqlQuery (SqlExpr (PreprocessedFrom (join a b)))
fromJoin (EPreprocessedFrom lhsRet lhsFrom)
         (EPreprocessedFrom rhsRet rhsFrom) = Q $ do
  let ret   = smartJoin lhsRet rhsRet
      from' = FromJoin lhsFrom             -- LHS
                       (reifyJoinKind ret) -- JOIN
                       rhsFrom             -- RHS
                       Nothing             -- ON
  return (EPreprocessedFrom ret from')

-- | (Internal) Finish a @JOIN@.
fromFinish
  :: SqlExpr (PreprocessedFrom a)
  -> SqlQuery a
fromFinish (EPreprocessedFrom ret f') = Q $ do
  W.tell mempty { sdFromClause = f' }
  return ret

innerJoinQuery :: (ToAlias a a', SqlSelect a' r, ToAliasReference a' b) 
               => SqlQuery a 
               -> SqlQuery b
innerJoinQuery = joinQuery InnerJoinKind

leftOuterJoinQuery :: (ToAlias a a', SqlSelect a' r, ToAliasReference a' b, ToMaybeExpr b b') 
                   => SqlQuery a 
                   -> SqlQuery b'
leftOuterJoinQuery = (fmap toMaybeExpr) . joinQuery LeftOuterJoinKind

rightOuterJoinQuery :: (ToAlias a a', SqlSelect a' r, ToAliasReference a' b, ToMaybeExpr b b')                                       => SqlQuery a 
                    -> SqlQuery b'
rightOuterJoinQuery = (fmap toMaybeExpr) . joinQuery RightOuterJoinKind

fullOuterJoinQuery :: (ToAlias a a', SqlSelect a' r, ToAliasReference a' b, ToMaybeExpr b b') 
                   => SqlQuery a 
                   -> SqlQuery b'
fullOuterJoinQuery = (fmap toMaybeExpr) . joinQuery FullOuterJoinKind

crossJoinQuery :: (ToAlias a a', SqlSelect a' r, ToAliasReference a' b) 
               => SqlQuery a 
               -> SqlQuery b
crossJoinQuery = joinQuery FullOuterJoinKind

joinQuery :: (ToAlias a a', SqlSelect a' r, ToAliasReference a' b) 
          => JoinKind 
          -> SqlQuery a 
          -> SqlQuery b
joinQuery joinKind subquery = do
    (ret, sideData) <- Q $ W.censor (\_ -> mempty) $ W.listen $ unQ subquery
    aliasedValue <- toAlias ret
    let aliasedQuery = Q $ W.WriterT $ pure (aliasedValue, sideData)
    subqueryAlias <- newIdentFor (DBName "subquery")
    let fromClause = FromQuery subqueryAlias (\info -> toRawSql SELECT info aliasedQuery)
    Q $ W.tell mempty {sdFromClause = FromJoinPartial joinKind fromClause}
    toAliasReference subqueryAlias aliasedValue

class ToMaybeExpr a b | a -> b where
  toMaybeExpr :: a -> b
        
instance ToMaybeExpr (SqlExpr a) (SqlExpr (Maybe a)) where
  toMaybeExpr e = EMaybe e

instance ( ToMaybeExpr a a', ToMaybeExpr b b') => ToMaybeExpr (a,b) (a',b') where
  toMaybeExpr (a,b) = (toMaybeExpr a, toMaybeExpr b)

instance ( ToMaybeExpr a a'
         , ToMaybeExpr b b'
         , ToMaybeExpr c c'
         ) => ToMaybeExpr (a,b,c) (a',b',c') where
  toMaybeExpr (a,b,c) = (toMaybeExpr a, toMaybeExpr b, toMaybeExpr c)

instance ( ToMaybeExpr a a'
         , ToMaybeExpr b b'
         , ToMaybeExpr c c'
         , ToMaybeExpr d d'
         ) => ToMaybeExpr (a,b,c,d) (a',b',c',d') where
  toMaybeExpr (a,b,c,d) = ( toMaybeExpr a
                          , toMaybeExpr b
                          , toMaybeExpr c
                          , toMaybeExpr d
                          )

instance ( ToMaybeExpr a a'
         , ToMaybeExpr b b'
         , ToMaybeExpr c c'
         , ToMaybeExpr d d'
         , ToMaybeExpr e e'
         ) => ToMaybeExpr (a,b,c,d,e) (a',b',c',d',e') where
  toMaybeExpr (a,b,c,d,e) = ( toMaybeExpr a
                            , toMaybeExpr b
                            , toMaybeExpr c
                            , toMaybeExpr d
                            , toMaybeExpr e
                            )
fromQuery
  :: (SqlSelect a' r, SqlSelect b' r', ToAlias a a', ToAliasReference b b')
  => SqlQuery a
  -> (a' -> SqlQuery b)
  -> SqlQuery b'
fromQuery subquery f = do
    -- We want to update the IdentState without writing the query to side data
    (ret, sideData) <- Q $ W.censor (\_ -> mempty) $ W.listen $ unQ subquery
    aliasedValue <- toAlias ret
    -- Make a fake query with the aliased results, this allows us to ensure that the query is only run once
    let aliasedQuery = Q $ W.WriterT $ pure (aliasedValue, sideData)
    -- Add the FromQuery that renders the subquery to our side data
    subqueryAlias <- newIdentFor (DBName "subquery")
    Q $ W.tell mempty{sdFromClause = FromQuery subqueryAlias (\info -> toRawSql SELECT info aliasedQuery)}
    -- Pass the aliased results of the subquery to the outer query
    outerQueryResults <- f aliasedValue
    -- create aliased references from the outer query results (e.g value from subquery will be `subquery`.`value`), 
    -- this is probably overkill as the aliases should already be unique but seems to be good practice.
    toAliasReference subqueryAlias outerQueryResults

-- Tedious tuple magic
class ToAlias a b | a -> b where
  toAlias :: a -> SqlQuery b

instance ToAlias (SqlExpr (Value a)) (SqlExpr (Value a)) where
  toAlias v@(EAliasedValue _ _) = pure v
  toAlias v = do 
    ident <- newIdentFor (DBName "value")
    pure $ EAliasedValue ident v

instance ToAlias (SqlExpr (Entity a)) (SqlExpr (Entity a)) where
  toAlias v@(EAliasedEntityReference _ _) = pure v
  toAlias v@(EAliasedEntity _ _) = pure v
  toAlias (EEntity tableIdent) = do 
    ident <- newIdentFor (DBName "value")
    pure $ EAliasedEntity ident tableIdent

instance ( ToAlias a a', ToAlias b b') => ToAlias (a,b) (a',b') where
  toAlias (a,b) = (,) <$> toAlias a <*> toAlias b

instance ( ToAlias a a'
         , ToAlias b b'
         , ToAlias c c'
         ) => ToAlias (a,b,c) (a',b',c') where
  toAlias x = to3 <$> (toAlias $ from3 x)

instance ( ToAlias a a'
         , ToAlias b b'
         , ToAlias c c'
         , ToAlias d d'
         ) => ToAlias (a,b,c,d) (a',b',c',d') where
  toAlias x = to4 <$> (toAlias $ from4 x)

instance ( ToAlias a a'
         , ToAlias b b'
         , ToAlias c c'
         , ToAlias d d'
         , ToAlias e e'
         ) => ToAlias (a,b,c,d,e) (a',b',c',d',e') where
  toAlias x = to5 <$> (toAlias $ from5 x)

-- more tedious tuple magic 
class ToAliasReference a b | a -> b where
  toAliasReference :: Ident -> a -> SqlQuery b

instance ToAliasReference (SqlExpr (Value a)) (SqlExpr (Value a)) where
  toAliasReference aliasSource (EAliasedValue aliasIdent _) = pure $ EValueReference aliasSource (\_ -> aliasIdent)
  toAliasReference _           v@(ERaw _ _)                 = toAlias v
  toAliasReference _           v@(ECompositeKey _)          = toAlias v
  toAliasReference _           v@(EValueReference _ _)      = pure v 

instance ToAliasReference (SqlExpr (Entity a)) (SqlExpr (Entity a)) where
  toAliasReference aliasSource (EAliasedEntity ident _) = pure $ EAliasedEntityReference aliasSource ident
  toAliasReference _ e@(EEntity _) = toAlias e 
  toAliasReference _ e@(EAliasedEntityReference _ _) = pure e

instance ( ToAliasReference a a', ToAliasReference b b') => ToAliasReference (a, b) ( a', b' ) where
  toAliasReference ident (a,b) = (,) <$> (toAliasReference ident a) <*> (toAliasReference ident b)

instance ( ToAliasReference a a'
         , ToAliasReference b b'
         , ToAliasReference c c'
         ) => ToAliasReference (a,b,c) ( a', b', c') where
  toAliasReference ident x = fmap to3 $ toAliasReference ident $ from3 x

instance ( ToAliasReference a a'
         , ToAliasReference b b'
         , ToAliasReference c c'
         , ToAliasReference d d'
         ) => ToAliasReference (a,b,c,d) (a',b',c',d') where
  toAliasReference ident x = fmap to4 $ toAliasReference ident $ from4 x

instance ( ToAliasReference a a'
         , ToAliasReference b b'
         , ToAliasReference c c'
         , ToAliasReference d d'
         , ToAliasReference e e'
         ) => ToAliasReference (a,b,c,d,e) (a',b',c',d',e') where
  toAliasReference ident x = fmap to5 $ toAliasReference ident $ from5 x


-- | @WHERE@ clause: restrict the query's result.
where_ :: SqlExpr (Value Bool) -> SqlQuery ()
where_ expr = Q $ W.tell mempty { sdWhereClause = Where expr }

-- | An @ON@ clause, useful to describe how two tables are related. Cross joins
-- and tuple-joins do not need an 'on' clause, but 'InnerJoin' and the various
-- outer joins do.
--
-- If you don't include an 'on' clause (or include too many!) then a runtime
-- exception will be thrown.
--
-- As an example, consider this simple join:
--
-- @
-- 'select' $
-- 'from' $ \\(foo `'InnerJoin`` bar) -> do
--   'on' (foo '^.' FooId '==.' bar '^.' BarFooId)
--   ...
-- @
--
-- We need to specify the clause for joining the two columns together. If we had
-- this:
--
-- @
-- 'select' $
-- 'from' $ \\(foo `'CrossJoin`` bar) -> do
--   ...
-- @
--
-- Then we can safely omit the 'on' clause, because the cross join will make
-- pairs of all records possible.
--
-- You can do multiple 'on' clauses in a query. This query joins three tables,
-- and has two 'on' clauses:
--
-- @
-- 'select' $
-- 'from' $ \\(foo `'InnerJoin`` bar `'InnerJoin`` baz) -> do
--   'on' (baz '^.' BazId '==.' bar '^.' BarBazId)
--   'on' (foo '^.' FooId '==.' bar '^.' BarFooId)
--   ...
-- @
--
-- Old versions of esqueleto required that you provide the 'on' clauses in
-- reverse order. This restriction has been lifted - you can now provide 'on'
-- clauses in any order, and the SQL should work itself out. The above query is
-- now totally equivalent to this:
--
-- @
-- 'select' $
-- 'from' $ \\(foo `'InnerJoin`` bar `'InnerJoin`` baz) -> do
--   'on' (foo '^.' FooId '==.' bar '^.' BarFooId)
--   'on' (baz '^.' BazId '==.' bar '^.' BarBazId)
--   ...
-- @
on :: SqlExpr (Value Bool) -> SqlQuery ()
on expr = Q $ W.tell mempty { sdFromClause = OnClause expr }

-- | @GROUP BY@ clause. You can enclose multiple columns
-- in a tuple.
--
-- @
-- select $ 'from' \\(foo `'InnerJoin`` bar) -> do
--   'on' (foo '^.' FooBarId '==.' bar '^.' BarId)
--   'groupBy' (bar '^.' BarId, bar '^.' BarName)
--   return (bar '^.' BarId, bar '^.' BarName, countRows)
-- @
--
-- With groupBy you can sort by aggregate functions, like so
-- (we used @let@ to restrict the more general 'countRows' to
-- @SqlSqlExpr (Value Int)@ to avoid ambiguity---the second use of
-- 'countRows' has its type restricted by the @:: Int@ below):
--
-- @
-- r \<- select $ 'from' \\(foo `'InnerJoin`` bar) -> do
--   'on' (foo '^.' FooBarId '==.' bar '^.' BarId)
--   'groupBy' $ bar '^.' BarName
--   let countRows' = 'countRows'
--   'orderBy' ['asc' countRows']
--   return (bar '^.' BarName, countRows')
-- forM_ r $ \\('Value' name, 'Value' count) -> do
--   print name
--   print (count :: Int)
-- @
groupBy :: (ToSomeValues a) => a -> SqlQuery ()
groupBy expr = Q $ W.tell mempty { sdGroupByClause = GroupBy $ toSomeValues expr }

-- | @ORDER BY@ clause. See also 'asc' and 'desc'.
--
-- Multiple calls to 'orderBy' get concatenated on the final
-- query, including 'distinctOnOrderBy'.
orderBy :: [SqlExpr OrderBy] -> SqlQuery ()
orderBy exprs = Q $ W.tell mempty { sdOrderByClause = exprs }

-- | Ascending order of this field or SqlExpression.
asc :: PersistField a => SqlExpr (Value a) -> SqlExpr OrderBy
asc  = EOrderBy ASC

-- | Descending order of this field or SqlExpression.
desc :: PersistField a => SqlExpr (Value a) -> SqlExpr OrderBy
desc = EOrderBy DESC

-- | @LIMIT@.  Limit the number of returned rows.
limit :: Int64 -> SqlQuery ()
limit  n = Q $ W.tell mempty { sdLimitClause = Limit (Just n) Nothing  }

-- | @OFFSET@.  Usually used with 'limit'.
offset :: Int64 -> SqlQuery ()
offset n = Q $ W.tell mempty { sdLimitClause = Limit Nothing  (Just n) }

-- | @DISTINCT@.  Change the current @SELECT@ into @SELECT
-- DISTINCT@.  For example:
--
-- @
-- select $ distinct $
--   'from' \\foo -> do
--   ...
-- @
--
-- Note that this also has the same effect:
--
-- @
-- select $
--   'from' \\foo -> do
--   distinct (return ())
--   ...
-- @
--
-- /Since: 2.2.4/
distinct :: SqlQuery a -> SqlQuery a
distinct act = Q (W.tell mempty { sdDistinctClause = DistinctStandard }) >> act

-- | @DISTINCT ON@.  Change the current @SELECT@ into
-- @SELECT DISTINCT ON (SqlExpressions)@.  For example:
--
-- @
-- select $
--   'from' \\foo ->
--   'distinctOn' ['don' (foo ^. FooName), 'don' (foo ^. FooState)] $ do
--   ...
-- @
--
-- You can also chain different calls to 'distinctOn'.  The
-- above is equivalent to:
--
-- @
-- select $
--   'from' \\foo ->
--   'distinctOn' ['don' (foo ^. FooName)] $
--   'distinctOn' ['don' (foo ^. FooState)] $ do
--   ...
-- @
--
-- Each call to 'distinctOn' adds more SqlExpressions.  Calls to
-- 'distinctOn' override any calls to 'distinct'.
--
-- Note that PostgreSQL requires the SqlExpressions on @DISTINCT
-- ON@ to be the first ones to appear on a @ORDER BY@.  This is
-- not managed automatically by esqueleto, keeping its spirit
-- of trying to be close to raw SQL.
--
-- Supported by PostgreSQL only.
--
-- /Since: 2.2.4/
distinctOn :: [SqlExpr DistinctOn] -> SqlQuery a -> SqlQuery a
distinctOn exprs act = Q (W.tell mempty { sdDistinctClause = DistinctOn exprs }) >> act

-- | Erase an SqlExpression's type so that it's suitable to
-- be used by 'distinctOn'.
--
-- /Since: 2.2.4/
don :: SqlExpr (Value a) -> SqlExpr DistinctOn
don = EDistinctOn

-- | A convenience function that calls both 'distinctOn' and
-- 'orderBy'.  In other words,
--
-- @
-- 'distinctOnOrderBy' [asc foo, desc bar, desc quux] $ do
--   ...
-- @
--
-- is the same as:
--
-- @
-- 'distinctOn' [don foo, don  bar, don  quux] $ do
--   'orderBy'  [asc foo, desc bar, desc quux]
--   ...
-- @
--
-- /Since: 2.2.4/
distinctOnOrderBy :: [SqlExpr OrderBy] -> SqlQuery a -> SqlQuery a
distinctOnOrderBy exprs act =
  distinctOn (toDistinctOn <$> exprs) $ do
    orderBy exprs
    act
  where
    toDistinctOn :: SqlExpr OrderBy -> SqlExpr DistinctOn
    toDistinctOn (EOrderBy _ f) = EDistinctOn f
    toDistinctOn EOrderRandom =
      error "We can't select distinct by a random order!"

-- | @ORDER BY random()@ clause.
--
-- /Since: 1.3.10/
rand :: SqlExpr OrderBy
rand = EOrderRandom

-- | @HAVING@.
--
-- /Since: 1.2.2/
having :: SqlExpr (Value Bool) -> SqlQuery ()
having expr = Q $ W.tell mempty { sdHavingClause = Where expr }

-- | Add a locking clause to the query.  Please read
-- 'LockingKind' documentation and your RDBMS manual.
--
-- If multiple calls to 'locking' are made on the same query,
-- the last one is used.
--
-- /Since: 2.2.7/
locking :: LockingKind -> SqlQuery ()
locking kind = Q $ W.tell mempty { sdLockingClause = Monoid.Last (Just kind) }

{-#
  DEPRECATED
    sub_select
    "sub_select \n \
sub_select is an unsafe function to use. If used with a SqlQuery that \n \
returns 0 results, then it may return NULL despite not mentioning Maybe \n \
in the return type. If it returns more than 1 result, then it will throw a \n \
SQL error.\n\n Instead, consider using one of the following alternatives: \n \
- subSelect: attaches a LIMIT 1 and the Maybe return type, totally safe.  \n \
- subSelectMaybe: Attaches a LIMIT 1, useful for a query that already \n \
  has a Maybe in the return type. \n \
- subSelectCount: Performs a count of the query - this is always safe. \n \
- subSelectUnsafe: Performs no checks or guarantees. Safe to use with \n \
  countRows and friends."
  #-}
-- | Execute a subquery @SELECT@ in an SqlExpression.  Returns a
-- simple value so should be used only when the @SELECT@ query
-- is guaranteed to return just one row.
--
-- Deprecated in 3.2.0.
sub_select :: PersistField a => SqlQuery (SqlExpr (Value a)) -> SqlExpr (Value a)
sub_select         = sub SELECT

-- | Execute a subquery @SELECT@ in a 'SqlExpr'. The query passed to this
-- function will only return a single result - it has a @LIMIT 1@ passed in to
-- the query to make it safe, and the return type is 'Maybe' to indicate that
-- the subquery might result in 0 rows.
--
-- If you find yourself writing @'joinV' . 'subSelect'@, then consider using
-- 'subSelectMaybe'.
--
-- If you're performing a 'countRows', then you can use 'subSelectCount' which
-- is safe.
--
-- If you know that the subquery will always return exactly one row (eg
-- a foreign key constraint guarantees that you'll get exactly one row), then
-- consider 'subSelectUnsafe', along with a comment explaining why it is safe.
--
-- @since 3.2.0
subSelect
  :: PersistField a
  => SqlQuery (SqlExpr (Value a))
  -> SqlExpr (Value (Maybe a))
subSelect query = just (subSelectUnsafe (query <* limit 1))

-- | Execute a subquery @SELECT@ in a 'SqlExpr'. This function is a shorthand
-- for the common @'joinV' . 'subSelect'@ idiom, where you are calling
-- 'subSelect' on an expression that would be 'Maybe' already.
--
-- As an example, you would use this function when calling 'sum_' or 'max_',
-- which have 'Maybe' in the result type (for a 0 row query).
--
-- @since 3.2.0
subSelectMaybe
  :: PersistField a
  => SqlQuery (SqlExpr (Value (Maybe a)))
  -> SqlExpr (Value (Maybe a))
subSelectMaybe = joinV . subSelect

-- | Performs a @COUNT@ of the given query in a @subSelect@ manner. This is
-- always guaranteed to return a result value, and is completely safe.
--
-- @since 3.2.0
subSelectCount
  :: (Num a, PersistField a)
  => SqlQuery ignored
  -> SqlExpr (Value a)
subSelectCount query = do
  subSelectUnsafe $ do
    _ <- query
    pure countRows

-- | Execute a subquery @SELECT@ in a 'SqlExpr' that returns a list. This is an
-- alias for 'subList_select' and is provided for symmetry with the other safe
-- subselect functions.
--
-- @since 3.2.0
subSelectList
  :: PersistField a
  => SqlQuery (SqlExpr (Value a))
  -> SqlExpr (ValueList a)
subSelectList = subList_select

-- | Performs a sub-select using the given foreign key on the entity. This is
-- useful to extract values that are known to be present by the database schema.
--
-- As an example, consider the following persistent definition:
--
-- @
-- User
--   profile ProfileId
--
-- Profile
--   name    Text
-- @
--
-- The following query will return the name of the user.
--
-- @
-- getUserWithName =
--     'select' $
--     'from' $ \user ->
--     'pure' (user, 'subSelectForeign' user UserProfile (^. ProfileName)
-- @
--
-- @since 3.2.0
subSelectForeign
  ::
  ( BackendCompatible SqlBackend (PersistEntityBackend val1)
  , PersistEntity val1, PersistEntity val2, PersistField a
  )
  => SqlExpr (Entity val2)
  -- ^ An expression representing the table you have access to now.
  -> EntityField val2 (Key val1)
  -- ^ The foreign key field on the table.
  -> (SqlExpr (Entity val1) -> SqlExpr (Value a))
  -- ^ A function to extract a value from the foreign reference table.
  -> SqlExpr (Value a)
subSelectForeign expr foreignKey k =
  subSelectUnsafe $
  from $ \table -> do
  where_ $ expr ^. foreignKey ==. table ^. persistIdField
  pure (k table)

-- | Execute a subquery @SELECT@ in a 'SqlExpr'. This function is unsafe,
-- because it can throw runtime exceptions in two cases:
--
-- 1. If the query passed has 0 result rows, then it will return a @NULL@ value.
--    The @persistent@ parsing operations will fail on an unexpected @NULL@.
-- 2. If the query passed returns more than one row, then the SQL engine will
--    fail with an error like "More than one row returned by a subquery used as
--    an expression".
--
-- This function is safe if you guarantee that exactly one row will be returned,
-- or if the result already has a 'Maybe' type for some reason.
--
-- For variants with the safety encoded already, see 'subSelect' and
-- 'subSelectMaybe'. For the most common safe use of this, see 'subSelectCount'.
--
-- @since 3.2.0
subSelectUnsafe :: PersistField a => SqlQuery (SqlExpr (Value a)) -> SqlExpr (Value a)
subSelectUnsafe = sub SELECT

-- | Project a field of an entity.
(^.)
  :: forall typ val. (PersistEntity val, PersistField typ)
  => SqlExpr (Entity val)
  -> EntityField val typ
  -> SqlExpr (Value typ)
e ^. field
  | isComposite   = ECompositeKey $ \info ->  dot info <$> compositeFields pdef
  | isReference e = makeValueReference (persistFieldDef field) e
  | otherwise     = ERaw Never    $ \info -> (dot info  $  persistFieldDef field, [])
  where
    isComposite = isIdField field && hasCompositeKey ed

    isReference (EAliasedEntityReference _ _) = True
    isReference _ = False

    makeValueReference :: FieldDef -> SqlExpr (Entity val) -> SqlExpr (Value typ)
    makeValueReference x (EAliasedEntityReference sourceIdent baseIdent) =
      EValueReference sourceIdent (aliasedEntityColumnIdent baseIdent x)  
    makeValueReference _ _ = undefined -- Protected by isReference guard

    dot info x  = 
      case e of
        EEntity ident ->
          useIdent info ident <> "." <> fromDBName info (fieldDB x)
        EAliasedEntity ident _ ->
          useIdent info $ aliasedEntityColumnIdent ident x info
        EAliasedEntityReference _ _ ->
          undefined -- defined above

    ed          = entityDef $ getEntityVal (Proxy :: Proxy (SqlExpr (Entity val)))
    Just pdef   = entityPrimary ed


-- | Project an SqlExpression that may be null, guarding against null cases.
withNonNull :: PersistField typ
            => SqlExpr (Value (Maybe typ))
            -> (SqlExpr (Value typ) -> SqlQuery a)
            -> SqlQuery a
withNonNull field f = do
  where_ $ not_ $ isNothing field
  f $ veryUnsafeCoerceSqlExprValue field

-- | Project a field of an entity that may be null.
(?.) :: (PersistEntity val, PersistField typ) =>
        SqlExpr (Maybe (Entity val)) -> EntityField val typ -> SqlExpr (Value (Maybe typ))
EMaybe r ?. field = just (r ^. field)

-- | Lift a constant value from Haskell-land to the query.
val  :: PersistField typ => typ -> SqlExpr (Value typ)
val v = ERaw Never $ const ("?", [toPersistValue v])

-- | @IS NULL@ comparison.
isNothing :: PersistField typ => SqlExpr (Value (Maybe typ)) -> SqlExpr (Value Bool)
isNothing v = 
    case v of 
      ERaw p f             -> isNullExpr $ first (parensM p) . f
      EAliasedValue i _    -> isNullExpr $ aliasedValueIdentToRawSql i
      EValueReference i i' -> isNullExpr $ valueReferenceToRawSql i i'
      ECompositeKey f      -> ERaw Parens $ flip (,) [] . (intersperseB " AND " . map (<> " IS NULL")) . f
  where 
    isNullExpr :: (IdentInfo -> (TLB.Builder, [PersistValue])) -> SqlExpr (Value Bool)
    isNullExpr g = ERaw Parens $ first ((<> " IS NULL")) . g

-- | Analogous to 'Just', promotes a value of type @typ@ into
-- one of type @Maybe typ@.  It should hold that @'val' . Just
-- === just . 'val'@.
just :: SqlExpr (Value typ) -> SqlExpr (Value (Maybe typ))
just (ERaw p f)             = ERaw p f
just (ECompositeKey f)      = ECompositeKey f
just (EAliasedValue i v)    = EAliasedValue i (just v)
just (EValueReference i i') = EValueReference i i'

-- | @NULL@ value.
nothing :: SqlExpr (Value (Maybe typ))
nothing = unsafeSqlValue "NULL"

-- | Join nested 'Maybe's in a 'Value' into one. This is useful when
-- calling aggregate functions on nullable fields.
joinV :: SqlExpr (Value (Maybe (Maybe typ))) -> SqlExpr (Value (Maybe typ))
joinV (ERaw p f)             = ERaw p f
joinV (ECompositeKey f)      = ECompositeKey f
joinV (EAliasedValue i v)    = EAliasedValue i (joinV v)
joinV (EValueReference i i') = EValueReference i i'


countHelper :: Num a => TLB.Builder -> TLB.Builder -> SqlExpr (Value typ) -> SqlExpr (Value a) 
countHelper open close v = 
    case v of
        ERaw _ f -> countRawSql f 
        EAliasedValue i _ -> countRawSql $ aliasedValueIdentToRawSql i
        EValueReference i i' -> countRawSql $ valueReferenceToRawSql i i'
        ECompositeKey _ -> countRows 
  where 
    countRawSql :: (IdentInfo -> (TLB.Builder, [PersistValue])) -> SqlExpr (Value a)
    countRawSql x = ERaw Never $ first (\b -> "COUNT" <> open <> parens b <> close) . x

-- | @COUNT(*)@ value.
countRows :: Num a => SqlExpr (Value a)
countRows     = unsafeSqlValue "COUNT(*)"

-- | @COUNT@.
count :: Num a => SqlExpr (Value typ) -> SqlExpr (Value a)
count         = countHelper ""           ""

-- | @COUNT(DISTINCT x)@.
--
-- /Since: 2.4.1/
countDistinct :: Num a => SqlExpr (Value typ) -> SqlExpr (Value a)
countDistinct = countHelper "(DISTINCT " ")"

not_ :: SqlExpr (Value Bool) -> SqlExpr (Value Bool)
not_ v = ERaw Never (\info -> first ("NOT " <>) $ x info)
  where
    x info =
      case v of
        ERaw p f ->
          let (b, vals) = f info
          in (parensM p b, vals)
        ECompositeKey _      -> throw (CompositeKeyErr NotError)
        EAliasedValue i _    -> aliasedValueIdentToRawSql i info
        EValueReference i i' -> valueReferenceToRawSql i i' info

(==.) :: PersistField typ => SqlExpr (Value typ) -> SqlExpr (Value typ) -> SqlExpr (Value Bool)
(==.) = unsafeSqlBinOpComposite " = " " AND "

(>=.) :: PersistField typ => SqlExpr (Value typ) -> SqlExpr (Value typ) -> SqlExpr (Value Bool)
(>=.) = unsafeSqlBinOp " >= "

(>.)  :: PersistField typ => SqlExpr (Value typ) -> SqlExpr (Value typ) -> SqlExpr (Value Bool)
(>.)  = unsafeSqlBinOp " > "

(<=.) :: PersistField typ => SqlExpr (Value typ) -> SqlExpr (Value typ) -> SqlExpr (Value Bool)
(<=.) = unsafeSqlBinOp " <= "

(<.)  :: PersistField typ => SqlExpr (Value typ) -> SqlExpr (Value typ) -> SqlExpr (Value Bool)
(<.)  = unsafeSqlBinOp " < "
(!=.) :: PersistField typ => SqlExpr (Value typ) -> SqlExpr (Value typ) -> SqlExpr (Value Bool)
(!=.) = unsafeSqlBinOpComposite " != " " OR "

(&&.) :: SqlExpr (Value Bool) -> SqlExpr (Value Bool) -> SqlExpr (Value Bool)
(&&.) = unsafeSqlBinOp " AND "

(||.) :: SqlExpr (Value Bool) -> SqlExpr (Value Bool) -> SqlExpr (Value Bool)
(||.) = unsafeSqlBinOp " OR "

(+.)  :: PersistField a => SqlExpr (Value a) -> SqlExpr (Value a) -> SqlExpr (Value a)
(+.)  = unsafeSqlBinOp " + "

(-.)  :: PersistField a => SqlExpr (Value a) -> SqlExpr (Value a) -> SqlExpr (Value a)
(-.)  = unsafeSqlBinOp " - "

(/.)  :: PersistField a => SqlExpr (Value a) -> SqlExpr (Value a) -> SqlExpr (Value a)
(/.)  = unsafeSqlBinOp " / "

(*.)  :: PersistField a => SqlExpr (Value a) -> SqlExpr (Value a) -> SqlExpr (Value a)
(*.)  = unsafeSqlBinOp " * "

-- | @BETWEEN@.
--
-- @since: 3.1.0
between :: PersistField a => SqlExpr (Value a) -> (SqlExpr (Value a), SqlExpr (Value a)) -> SqlExpr (Value Bool)
a `between` (b, c) = a >=. b &&. a <=. c

random_  :: (PersistField a, Num a) => SqlExpr (Value a)
random_  = unsafeSqlValue "RANDOM()"

round_   :: (PersistField a, Num a, PersistField b, Num b) => SqlExpr (Value a) -> SqlExpr (Value b)
round_   = unsafeSqlFunction "ROUND"

ceiling_ :: (PersistField a, Num a, PersistField b, Num b) => SqlExpr (Value a) -> SqlExpr (Value b)
ceiling_ = unsafeSqlFunction "CEILING"

floor_   :: (PersistField a, Num a, PersistField b, Num b) => SqlExpr (Value a) -> SqlExpr (Value b)
floor_   = unsafeSqlFunction "FLOOR"

sum_     :: (PersistField a, PersistField b) => SqlExpr (Value a) -> SqlExpr (Value (Maybe b))
sum_     = unsafeSqlFunction "SUM"
min_     :: (PersistField a) => SqlExpr (Value a) -> SqlExpr (Value (Maybe a))
min_     = unsafeSqlFunction "MIN"
max_     :: (PersistField a) => SqlExpr (Value a) -> SqlExpr (Value (Maybe a))
max_     = unsafeSqlFunction "MAX"
avg_     :: (PersistField a, PersistField b) => SqlExpr (Value a) -> SqlExpr (Value (Maybe b))
avg_     = unsafeSqlFunction "AVG"

-- | Allow a number of one type to be used as one of another
-- type via an implicit cast.  An explicit cast is not made,
-- this function changes only the types on the Haskell side.
--
-- /Caveat/: Trying to use @castNum@ from @Double@ to @Int@
-- will not result in an integer, the original fractional
-- number will still be used!  Use 'round_', 'ceiling_' or
-- 'floor_' instead.
--
-- /Safety/: This operation is mostly safe due to the 'Num'
-- constraint between the types and the fact that RDBMSs
-- usually allow numbers of different types to be used
-- interchangeably.  However, there may still be issues with
-- the query not being accepted by the RDBMS or @persistent@
-- not being able to parse it.
--
-- /Since: 2.2.9/
castNum :: (Num a, Num b) => SqlExpr (Value a) -> SqlExpr (Value b)
castNum  = veryUnsafeCoerceSqlExprValue

-- | Same as 'castNum', but for nullable values.
--
-- /Since: 2.2.9/
castNumM :: (Num a, Num b) => SqlExpr (Value (Maybe a)) -> SqlExpr (Value (Maybe b))
castNumM = veryUnsafeCoerceSqlExprValue

-- | @COALESCE@ function. Evaluates the arguments in order and
-- returns the value of the first non-NULL SqlExpression, or NULL
-- (Nothing) otherwise. Some RDBMSs (such as SQLite) require
-- at least two arguments; please refer to the appropriate
-- documentation.
--
-- /Since: 1.4.3/
coalesce :: PersistField a => [SqlExpr (Value (Maybe a))] -> SqlExpr (Value (Maybe a))
coalesce              = unsafeSqlFunctionParens "COALESCE"

-- | Like @coalesce@, but takes a non-nullable SqlExpression
-- placed at the end of the SqlExpression list, which guarantees
-- a non-NULL result.
--
-- /Since: 1.4.3/
coalesceDefault :: PersistField a => [SqlExpr (Value (Maybe a))] -> SqlExpr (Value a) -> SqlExpr (Value a)
coalesceDefault exprs = unsafeSqlFunctionParens "COALESCE" . (exprs ++) . return . just

-- | @LOWER@ function.
lower_ :: SqlString s => SqlExpr (Value s) -> SqlExpr (Value s)
lower_  = unsafeSqlFunction "LOWER"

-- | @UPPER@ function.
-- /Since: 3.3.0/
upper_ :: SqlString s => SqlExpr (Value s) -> SqlExpr (Value s)
upper_  = unsafeSqlFunction "UPPER"

-- | @TRIM@ function.
-- /Since: 3.3.0/
trim_ :: SqlString s => SqlExpr (Value s) -> SqlExpr (Value s)
trim_  = unsafeSqlFunction "TRIM"

-- | @RTRIM@ function.
-- /Since: 3.3.0/
rtrim_ :: SqlString s => SqlExpr (Value s) -> SqlExpr (Value s)
rtrim_  = unsafeSqlFunction "RTRIM"

-- | @LTRIM@ function.
-- /Since: 3.3.0/
ltrim_ :: SqlString s => SqlExpr (Value s) -> SqlExpr (Value s)
ltrim_  = unsafeSqlFunction "LTRIM"

-- | @LENGTH@ function.
-- /Since: 3.3.0/
length_ :: (SqlString s, Num a) => SqlExpr (Value s) -> SqlExpr (Value a)
length_ = unsafeSqlFunction "LENGTH"

-- | @LEFT@ function.
-- /Since: 3.3.0/
left_ :: (SqlString s, Num a) => (SqlExpr (Value s), SqlExpr (Value a)) -> SqlExpr (Value s)
left_ = unsafeSqlFunction "LEFT"

-- | @RIGHT@ function.
-- /Since: 3.3.0/
right_ :: (SqlString s, Num a) => (SqlExpr (Value s), SqlExpr (Value a)) -> SqlExpr (Value s)
right_ = unsafeSqlFunction "RIGHT"

-- | @LIKE@ operator.
like :: SqlString s => SqlExpr (Value s) -> SqlExpr (Value s) -> SqlExpr (Value Bool)
like    = unsafeSqlBinOp    " LIKE "

-- | @ILIKE@ operator (case-insensitive @LIKE@).
--
-- Supported by PostgreSQL only.
--
-- /Since: 2.2.3/
ilike :: SqlString s => SqlExpr (Value s) -> SqlExpr (Value s) -> SqlExpr (Value Bool)
ilike   = unsafeSqlBinOp    " ILIKE "

-- | The string @'%'@.  May be useful while using 'like' and
-- concatenation ('concat_' or '++.', depending on your
-- database).  Note that you always have to type the parenthesis,
-- for example:
--
-- @
-- name `'like`` (%) ++. 'val' \"John\" ++. (%)
-- @
(%) :: SqlString s => SqlExpr (Value s)
(%)     = unsafeSqlValue    "'%'"

-- | The @CONCAT@ function with a variable number of
-- parameters.  Supported by MySQL and PostgreSQL.
concat_ :: SqlString s => [SqlExpr (Value s)] -> SqlExpr (Value s)
concat_ = unsafeSqlFunction "CONCAT"

-- | The @||@ string concatenation operator (named after
-- Haskell's '++' in order to avoid naming clash with '||.').
-- Supported by SQLite and PostgreSQL.
(++.) :: SqlString s => SqlExpr (Value s) -> SqlExpr (Value s) -> SqlExpr (Value s)
(++.)   = unsafeSqlBinOp    " || "

-- | Cast a string type into 'Text'.  This function
-- is very useful if you want to use @newtype@s, or if you want
-- to apply functions such as 'like' to strings of different
-- types.
--
-- /Safety:/ This is a slightly unsafe function, especially if
-- you have defined your own instances of 'SqlString'.  Also,
-- since 'Maybe' is an instance of 'SqlString', it's possible
-- to turn a nullable value into a non-nullable one.  Avoid
-- using this function if possible.
castString :: (SqlString s, SqlString r) => SqlExpr (Value s) -> SqlExpr (Value r)
castString = veryUnsafeCoerceSqlExprValue

-- | Execute a subquery @SELECT@ in an SqlExpression.  Returns a
-- list of values.
subList_select :: PersistField a => SqlQuery (SqlExpr (Value a)) -> SqlExpr (ValueList a)
subList_select         = EList . sub_select

-- | Lift a list of constant value from Haskell-land to the query.
valList :: PersistField typ => [typ] -> SqlExpr (ValueList typ)
valList []   = EEmptyList
valList vals = EList $ ERaw Parens $ const ( uncommas ("?" <$ vals)
                                           , map toPersistValue vals )

-- | Same as 'just' but for 'ValueList'.  Most of the time you
-- won't need it, though, because you can use 'just' from
-- inside 'subList_select' or 'Just' from inside 'valList'.
--
-- /Since: 2.2.12/
justList :: SqlExpr (ValueList typ) -> SqlExpr (ValueList (Maybe typ))
justList EEmptyList = EEmptyList
justList (EList v)  = EList (just v)

-- | @IN@ operator. For example if you want to select all @Person@s by a list
-- of IDs:
--
-- @
-- SELECT *
-- FROM Person
-- WHERE Person.id IN (?)
-- @
--
-- In @esqueleto@, we may write the same query above as:
--
-- @
-- select $
-- 'from' $ \\person -> do
-- 'where_' $ person '^.' PersonId `'in_`` 'valList' personIds
-- return person
-- @
--
-- Where @personIds@ is of type @[Key Person]@.
in_ :: PersistField typ => SqlExpr (Value typ) -> SqlExpr (ValueList typ) -> SqlExpr (Value Bool)
v `in_`   e = ifNotEmptyList e False $ unsafeSqlBinOp     " IN " v (veryUnsafeCoerceSqlExprValueList e)

-- | @NOT IN@ operator.
notIn :: PersistField typ => SqlExpr (Value typ) -> SqlExpr (ValueList typ) -> SqlExpr (Value Bool)
v `notIn` e = ifNotEmptyList e True  $ unsafeSqlBinOp " NOT IN " v (veryUnsafeCoerceSqlExprValueList e)

-- | @EXISTS@ operator.  For example:
--
-- @
-- select $
-- 'from' $ \\person -> do
-- 'where_' $ 'exists' $
--          'from' $ \\post -> do
--          'where_' (post '^.' BlogPostAuthorId '==.' person '^.' PersonId)
-- return person
-- @
exists :: SqlQuery () -> SqlExpr (Value Bool)
exists    = unsafeSqlFunction     "EXISTS " . existsHelper

-- | @NOT EXISTS@ operator.
notExists :: SqlQuery () -> SqlExpr (Value Bool)
notExists = unsafeSqlFunction "NOT EXISTS " . existsHelper

-- | @SET@ clause used on @UPDATE@s.  Note that while it's not
-- a type error to use this function on a @SELECT@, it will
-- most certainly result in a runtime error.
set :: PersistEntity val => SqlExpr (Entity val) -> [SqlExpr (Update val)] -> SqlQuery ()
set ent upds = Q $ W.tell mempty { sdSetClause = map apply upds }
  where
    apply (ESet f) = SetClause (f ent)

(=.)  :: (PersistEntity val, PersistField typ) => EntityField val typ -> SqlExpr (Value typ) -> SqlExpr (Update val)
field  =. expr = setAux field (const expr)

(+=.) :: (PersistEntity val, PersistField a) => EntityField val a -> SqlExpr (Value a) -> SqlExpr (Update val)
field +=. expr = setAux field (\ent -> ent ^. field +. expr)

(-=.) :: (PersistEntity val, PersistField a) => EntityField val a -> SqlExpr (Value a) -> SqlExpr (Update val)
field -=. expr = setAux field (\ent -> ent ^. field -. expr)

(*=.) :: (PersistEntity val, PersistField a) => EntityField val a -> SqlExpr (Value a) -> SqlExpr (Update val)
field *=. expr = setAux field (\ent -> ent ^. field *. expr)

(/=.) :: (PersistEntity val, PersistField a) => EntityField val a -> SqlExpr (Value a) -> SqlExpr (Update val)
field /=. expr = setAux field (\ent -> ent ^. field /. expr)

-- | Apply a 'PersistField' constructor to @SqlExpr Value@ arguments.
(<#) :: (a -> b) -> SqlExpr (Value a) -> SqlExpr (Insertion b)
(<#) _ (ERaw _ f)        = EInsert Proxy f
(<#) _ (ECompositeKey _) = throw (CompositeKeyErr ToInsertionError)
(<#) _ (EAliasedValue i _) = EInsert Proxy $ aliasedValueIdentToRawSql i
(<#) _ (EValueReference i i') = EInsert Proxy $ valueReferenceToRawSql i i'


-- | Apply extra @SqlExpr Value@ arguments to a 'PersistField' constructor
(<&>) :: SqlExpr (Insertion (a -> b)) -> SqlExpr (Value a) -> SqlExpr (Insertion b)
(EInsert _ f) <&> v = EInsert Proxy $ \x ->
  let (fb, fv) = f x
      (gb, gv) = g x
  in (fb <> ", " <> gb, fv ++ gv)
 where 
  g =
    case v of
      ERaw _ f' -> f'
      EAliasedValue i _ -> aliasedValueIdentToRawSql i
      EValueReference i i' -> valueReferenceToRawSql i i'
      ECompositeKey _ -> throw (CompositeKeyErr CombineInsertionError)

-- | @CASE@ statement.  For example:
--
-- @
-- select $
-- return $
-- 'case_'
--    [ 'when_'
--        ('exists' $
--        'from' $ \\p -> do
--        'where_' (p '^.' PersonName '==.' 'val' \"Mike\"))
--      'then_'
--        ('sub_select' $
--        'from' $ \\v -> do
--        let sub =
--                'from' $ \\c -> do
--                'where_' (c '^.' PersonName '==.' 'val' \"Mike\")
--                return (c '^.' PersonFavNum)
--        'where_' (v '^.' PersonFavNum >. 'sub_select' sub)
--        return $ 'count' (v '^.' PersonName) +. 'val' (1 :: Int)) ]
--    ('else_' $ 'val' (-1))
-- @
--
-- This query is a bit complicated, but basically it checks if a person
-- named @\"Mike\"@ exists, and if that person does, run the subquery to find
-- out how many people have a ranking (by Fav Num) higher than @\"Mike\"@.
--
-- __NOTE:__ There are a few things to be aware about this statement.
--
--    * This only implements the full CASE statement, it does not
--      implement the \"simple\" CASE statement.
--
--
--    * At least one 'when_' and 'then_' is mandatory otherwise it will
--      emit an error.
--
--
--    * The 'else_' is also mandatory, unlike the SQL statement in which
--      if the @ELSE@ is omitted it will return a @NULL@. You can
--      reproduce this via 'nothing'.
--
-- /Since: 2.1.2/
case_ :: PersistField a => [(SqlExpr (Value Bool), SqlExpr (Value a))] -> SqlExpr (Value a) -> SqlExpr (Value a)
case_ = unsafeSqlCase

-- | Convert an entity's key into another entity's.
--
-- This function is to be used when you change an entity's @Id@ to be
-- that of another entity.  For example:
--
-- @
-- Bar
--   barNum Int
-- Foo
--   bar BarId
--   fooNum Int
--   Primary bar
-- @
--
-- For this example, declare:
--
-- @
-- instance ToBaseId Foo where
--   type BaseEnt Foo = Bar
--   toBaseIdWitness = FooKey
-- @
--
-- Now you're able to write queries such as:
--
-- @
-- 'select' $
-- 'from' $ \(bar `'InnerJoin`` foo) -> do
-- 'on' ('toBaseId' (foo '^.' FooId) '==.' bar '^.' BarId)
-- return (bar, foo)
-- @
--
-- Note: this function may be unsafe to use in conditions not like the
-- one of the example above.
--
-- /Since: 2.4.3/
toBaseId :: ToBaseId ent => SqlExpr (Value (Key ent)) -> SqlExpr (Value (Key (BaseEnt ent)))
toBaseId = veryUnsafeCoerceSqlExprValue

{-# DEPRECATED random_ "Since 2.6.0: `random_` is not uniform across all databases! Please use a specific one such as 'Database.Esqueleto.PostgreSQL.random_', 'Database.Esqueleto.MySQL.random_', or 'Database.Esqueleto.SQLite.random_'" #-}

{-# DEPRECATED rand "Since 2.6.0: `rand` ordering function is not uniform across all databases! To avoid accidental partiality it will be removed in the next major version." #-}

-- Fixity declarations
infixl 9 ^.
infixl 7 *., /.
infixl 6 +., -.
infixr 5 ++.
infix  4 ==., >=., >., <=., <., !=.
infixr 3 &&., =., +=., -=., *=., /=.
infixr 2 ||., `like`, `ilike`
infixl 2 `InnerJoin`, `CrossJoin`, `LeftOuterJoin`, `RightOuterJoin`, `FullOuterJoin`

-- | Syntax sugar for 'case_'.
--
-- /Since: 2.1.2/
when_ :: expr (Value Bool) -> () -> expr a -> (expr (Value Bool), expr a)
when_ cond _ expr = (cond, expr)

-- | Syntax sugar for 'case_'.
--
-- /Since: 2.1.2/
then_ :: ()
then_ = ()

-- | Syntax sugar for 'case_'.
--
-- /Since: 2.1.2/
else_ :: expr a -> expr a
else_ = id


-- | A single value (as opposed to a whole entity).  You may use
-- @('^.')@ or @('?.')@ to get a 'Value' from an 'Entity'.
newtype Value a = Value { unValue :: a } deriving (Eq, Ord, Show, Typeable)


-- | /Since: 1.4.4/
instance Functor Value where
  fmap f (Value a) = Value (f a)

instance Applicative Value where
  (<*>) (Value f) (Value a) = Value (f a)
  pure = Value

instance Monad Value where
  (>>=) x f = valueJoin $ fmap f x
    where valueJoin (Value v) = v

-- | A list of single values.  There's a limited set of functions
-- able to work with this data type (such as 'subList_select',
-- 'valList', 'in_' and 'exists').
newtype ValueList a = ValueList a deriving (Eq, Ord, Show, Typeable)


-- | A wrapper type for for any @expr (Value a)@ for all a.
data SomeValue where
  SomeValue :: SqlExpr (Value a) -> SomeValue

-- | A class of things that can be converted into a list of SomeValue. It has
-- instances for tuples and is the reason why 'groupBy' can take tuples, like
-- @'groupBy' (foo '^.' FooId, foo '^.' FooName, foo '^.' FooType)@.
class ToSomeValues a where
  toSomeValues :: a -> [SomeValue]

instance ( ToSomeValues a
         , ToSomeValues b
         ) => ToSomeValues (a, b) where
  toSomeValues (a,b) = toSomeValues a ++ toSomeValues b

instance ( ToSomeValues a
         , ToSomeValues b
         , ToSomeValues c
         ) => ToSomeValues (a, b, c) where
  toSomeValues (a,b,c) = toSomeValues a ++ toSomeValues b ++ toSomeValues c

instance ( ToSomeValues a
         , ToSomeValues b
         , ToSomeValues c
         , ToSomeValues d
         ) => ToSomeValues (a, b, c, d) where
  toSomeValues (a,b,c,d) = toSomeValues a ++ toSomeValues b ++ toSomeValues c ++
    toSomeValues d

instance ( ToSomeValues a
         , ToSomeValues b
         , ToSomeValues c
         , ToSomeValues d
         , ToSomeValues e
         ) => ToSomeValues (a, b, c, d, e) where
  toSomeValues (a,b,c,d,e) = toSomeValues a ++ toSomeValues b ++
    toSomeValues c ++ toSomeValues d ++ toSomeValues e

instance ( ToSomeValues a
         , ToSomeValues b
         , ToSomeValues c
         , ToSomeValues d
         , ToSomeValues e
         , ToSomeValues f
         ) => ToSomeValues (a, b, c, d, e, f) where
  toSomeValues (a,b,c,d,e,f) = toSomeValues a ++ toSomeValues b ++
    toSomeValues c ++ toSomeValues d ++ toSomeValues e ++ toSomeValues f

instance ( ToSomeValues a
         , ToSomeValues b
         , ToSomeValues c
         , ToSomeValues d
         , ToSomeValues e
         , ToSomeValues f
         , ToSomeValues g
         ) => ToSomeValues (a, b, c, d, e, f, g) where
  toSomeValues (a,b,c,d,e,f,g) = toSomeValues a ++ toSomeValues b ++
    toSomeValues c ++ toSomeValues d ++ toSomeValues e ++ toSomeValues f ++
    toSomeValues g

instance ( ToSomeValues a
         , ToSomeValues b
         , ToSomeValues c
         , ToSomeValues d
         , ToSomeValues e
         , ToSomeValues f
         , ToSomeValues g
         , ToSomeValues h
         ) => ToSomeValues (a, b, c, d, e, f, g, h) where
  toSomeValues (a,b,c,d,e,f,g,h) = toSomeValues a ++ toSomeValues b ++
    toSomeValues c ++ toSomeValues d ++ toSomeValues e ++ toSomeValues f ++
    toSomeValues g ++ toSomeValues h

type family KnowResult a where
  KnowResult (i -> o) = KnowResult o
  KnowResult a = a

-- | A class for constructors or function which result type is known.
--
-- @since 3.1.3
class FinalResult a where
  finalR :: a -> KnowResult a

instance FinalResult (Unique val) where
  finalR = id

instance (FinalResult b) => FinalResult (a -> b) where
  finalR f = finalR (f undefined)

-- | Convert a constructor for a 'Unique' key on a record to the 'UniqueDef' that defines it. You
-- can supply just the constructor itself, or a value of the type - the library is capable of figuring
-- it out from there.
--
-- @since 3.1.3
toUniqueDef :: forall a val. (KnowResult a ~ (Unique val), PersistEntity val,FinalResult a) =>
  a -> UniqueDef
toUniqueDef uniqueConstructor = uniqueDef
  where
    proxy :: Proxy val
    proxy = Proxy
    unique :: Unique val
    unique = finalR uniqueConstructor
    -- there must be a better way to get the constrain name from a unique, make this not a list search
    filterF = (==) (persistUniqueToFieldNames unique) . uniqueFields
    uniqueDef = head . filter filterF . entityUniques . entityDef $ proxy

-- | Render updates to be use in a SET clause for a given sql backend.
--
-- @since 3.1.3
renderUpdates :: (BackendCompatible SqlBackend backend) =>
    backend
    -> [SqlExpr (Update val)]
    -> (TLB.Builder, [PersistValue])
renderUpdates conn = uncommas' . concatMap renderUpdate
    where
      mk :: SqlExpr (Value ()) -> [(TLB.Builder, [PersistValue])]
      mk (ERaw _ f)             = [f info]
      mk (ECompositeKey _)      = throw (CompositeKeyErr MakeSetError) -- FIXME
      mk (EAliasedValue i _)    = [aliasedValueIdentToRawSql i info]
      mk (EValueReference i i') = [valueReferenceToRawSql i i' info]

      renderUpdate :: SqlExpr (Update val) -> [(TLB.Builder, [PersistValue])]
      renderUpdate (ESet f) = mk (f undefined) -- second parameter of f is always unused
      info = (projectBackend conn, initialIdentState)

-- | Data type that represents an @INNER JOIN@ (see 'LeftOuterJoin' for an example).
data InnerJoin a b = a `InnerJoin` b

-- | Data type that represents a @CROSS JOIN@ (see 'LeftOuterJoin' for an example).
data CrossJoin a b = a `CrossJoin` b

-- | Data type that represents a @LEFT OUTER JOIN@. For example,
--
-- @
-- select $
-- 'from' $ \\(person `'LeftOuterJoin`` pet) ->
--   ...
-- @
--
-- is translated into
--
-- @
-- SELECT ...
-- FROM Person LEFT OUTER JOIN Pet
-- ...
-- @
--
-- See also: 'from'.
data LeftOuterJoin a b = a `LeftOuterJoin` b

-- | Data type that represents a @RIGHT OUTER JOIN@ (see 'LeftOuterJoin' for an example).
data RightOuterJoin a b = a `RightOuterJoin` b

-- | Data type that represents a @FULL OUTER JOIN@ (see 'LeftOuterJoin' for an example).
data FullOuterJoin a b = a `FullOuterJoin` b


-- | (Internal) A kind of @JOIN@.
data JoinKind =
    InnerJoinKind      -- ^ @INNER JOIN@
  | CrossJoinKind      -- ^ @CROSS JOIN@
  | LeftOuterJoinKind  -- ^ @LEFT OUTER JOIN@
  | RightOuterJoinKind -- ^ @RIGHT OUTER JOIN@
  | FullOuterJoinKind  -- ^ @FULL OUTER JOIN@
    deriving (Eq, Show)


-- | (Internal) Functions that operate on types (that should be)
-- of kind 'JoinKind'.
class IsJoinKind join where
  -- | (Internal) @smartJoin a b@ is a @JOIN@ of the correct kind.
  smartJoin :: a -> b -> join a b
  -- | (Internal) Reify a @JoinKind@ from a @JOIN@.  This
  -- function is non-strict.
  reifyJoinKind :: join a b -> JoinKind
instance IsJoinKind InnerJoin where
  smartJoin a b = a `InnerJoin` b
  reifyJoinKind _ = InnerJoinKind
instance IsJoinKind CrossJoin where
  smartJoin a b = a `CrossJoin` b
  reifyJoinKind _ = CrossJoinKind
instance IsJoinKind LeftOuterJoin where
  smartJoin a b = a `LeftOuterJoin` b
  reifyJoinKind _ = LeftOuterJoinKind
instance IsJoinKind RightOuterJoin where
  smartJoin a b = a `RightOuterJoin` b
  reifyJoinKind _ = RightOuterJoinKind
instance IsJoinKind FullOuterJoin where
  smartJoin a b = a `FullOuterJoin` b
  reifyJoinKind _ = FullOuterJoinKind


-- | Exception thrown whenever 'on' is used to create an @ON@
-- clause but no matching @JOIN@ is found.
data OnClauseWithoutMatchingJoinException =
  OnClauseWithoutMatchingJoinException String
  deriving (Eq, Ord, Show, Typeable)
instance Exception OnClauseWithoutMatchingJoinException where


-- | (Internal) Phantom type used to process 'from' (see 'fromStart').
data PreprocessedFrom a


-- | Phantom type used by 'orderBy', 'asc' and 'desc'.
data OrderBy


-- | Phantom type used by 'distinctOn' and 'don'.
data DistinctOn


-- | Phantom type for a @SET@ operation on an entity of the given
-- type (see 'set' and '(=.)').
data Update typ


-- | Phantom type used by 'insertSelect'.
data Insertion a


-- | Different kinds of locking clauses supported by 'locking'.
--
-- Note that each RDBMS has different locking support.  The
-- constructors of this datatype specify only the /syntax/ of the
-- locking mechanism, not its /semantics/.  For example, even
-- though both MySQL and PostgreSQL support 'ForUpdate', there
-- are no guarantees that they will behave the same.
--
-- /Since: 2.2.7/
data LockingKind =
    ForUpdate
    -- ^ @FOR UPDATE@ syntax.  Supported by MySQL, Oracle and
    -- PostgreSQL.
    --
    -- /Since: 2.2.7/
  | ForUpdateSkipLocked
    -- ^ @FOR UPDATE SKIP LOCKED@ syntax.  Supported by MySQL, Oracle and
    -- PostgreSQL.
    --
    -- /Since: 2.2.7/
  | ForShare
    -- ^ @FOR SHARE@ syntax.  Supported by PostgreSQL.
    --
    -- /Since: 2.2.7/
  | LockInShareMode
    -- ^ @LOCK IN SHARE MODE@ syntax.  Supported by MySQL.
    --
    -- /Since: 2.2.7/


-- | Phantom class of data types that are treated as strings by the
-- RDBMS.  It has no methods because it's only used to avoid type
-- errors such as trying to concatenate integers.
--
-- If you have a custom data type or @newtype@, feel free to make
-- it an instance of this class.
--
-- /Since: 2.4.0/
class PersistField a => SqlString a where

-- | /Since: 2.3.0/
instance (a ~ Char) => SqlString [a] where

-- | /Since: 2.3.0/
instance SqlString T.Text where

-- | /Since: 2.3.0/
instance SqlString TL.Text where

-- | /Since: 2.3.0/
instance SqlString B.ByteString where

-- | /Since: 2.3.0/
instance SqlString Html where

-- | /Since: 2.4.0/
instance SqlString a => SqlString (Maybe a) where

-- | Class that enables one to use 'toBaseId' to convert an entity's
-- key on a query into another (cf. 'toBaseId').
class ToBaseId ent where
  type BaseEnt ent :: *
  toBaseIdWitness :: Key (BaseEnt ent) -> Key ent


-- | @FROM@ clause: bring entities into scope.
--
-- This function internally uses two type classes in order to
-- provide some flexibility of how you may call it.  Internally
-- we refer to these type classes as the two different magics.
--
-- The innermost magic allows you to use @from@ with the
-- following types:
--
--  * @expr (Entity val)@, which brings a single entity into
--  scope.
--
--  * @expr (Maybe (Entity val))@, which brings a single entity
--  that may be @NULL@ into scope.  Used for @OUTER JOIN@s.
--
--  * A @JOIN@ of any other two types allowed by the innermost
--  magic, where a @JOIN@ may be an 'InnerJoin', a 'CrossJoin', a
--  'LeftOuterJoin', a 'RightOuterJoin', or a 'FullOuterJoin'.
--  The @JOINs@ have left fixity.
--
-- The outermost magic allows you to use @from@ on any tuples of
-- types supported by innermost magic (and also tuples of tuples,
-- and so on), up to 8-tuples.
--
-- Note that using @from@ for the same entity twice does work and
-- corresponds to a self-join.  You don't even need to use two
-- different calls to @from@, you may use a @JOIN@ or a tuple.
--
-- The following are valid examples of uses of @from@ (the types
-- of the arguments of the lambda are inside square brackets):
--
-- @
-- 'from' $ \\person -> ...
-- 'from' $ \\(person, blogPost) -> ...
-- 'from' $ \\(p `'LeftOuterJoin`` mb) -> ...
-- 'from' $ \\(p1 `'InnerJoin`` f `'InnerJoin`` p2) -> ...
-- 'from' $ \\((p1 `'InnerJoin`` f) `'InnerJoin`` p2) -> ...
-- @
--
-- The types of the arguments to the lambdas above are,
-- respectively:
--
-- @
-- person
--   :: ( Esqueleto query expr backend
--      , PersistEntity Person
--      , PersistEntityBackend Person ~ backend
--      ) => expr (Entity Person)
-- (person, blogPost)
--   :: (...) => (expr (Entity Person), expr (Entity BlogPost))
-- (p `'LeftOuterJoin`` mb)
--   :: (...) => InnerJoin (expr (Entity Person)) (expr (Maybe (Entity BlogPost)))
-- (p1 `'InnerJoin`` f `'InnerJoin`` p2)
--   :: (...) => InnerJoin
--                 (InnerJoin (expr (Entity Person))
--                            (expr (Entity Follow)))
--                 (expr (Entity Person))
-- (p1 `'InnerJoin`` (f `'InnerJoin`` p2)) ::
--   :: (...) => InnerJoin
--                 (expr (Entity Person))
--                 (InnerJoin (expr (Entity Follow))
--                            (expr (Entity Person)))
-- @
--
-- Note that some backends may not support all kinds of @JOIN@s.
from :: From a => (a -> SqlQuery b) -> SqlQuery b
from = (from_ >>=)


-- | (Internal) Class that implements the tuple 'from' magic (see
-- 'fromStart').
class From a where
  from_ :: SqlQuery a

instance ( FromPreprocess (SqlExpr (Entity val))
         ) => From (SqlExpr (Entity val)) where
  from_ = fromPreprocess >>= fromFinish

instance ( FromPreprocess (SqlExpr (Maybe (Entity val)))
         ) => From (SqlExpr (Maybe (Entity val))) where
  from_ = fromPreprocess >>= fromFinish

instance ( FromPreprocess (InnerJoin a b)
         ) => From (InnerJoin a b) where
  from_ = fromPreprocess >>= fromFinish

instance ( FromPreprocess (CrossJoin a b)
         ) => From (CrossJoin a b) where
  from_ = fromPreprocess >>= fromFinish

instance ( FromPreprocess (LeftOuterJoin a b)
         ) => From (LeftOuterJoin a b) where
  from_ = fromPreprocess >>= fromFinish

instance ( FromPreprocess (RightOuterJoin a b)
         ) => From (RightOuterJoin a b) where
  from_ = fromPreprocess >>= fromFinish

instance ( FromPreprocess (FullOuterJoin a b)
         ) => From (FullOuterJoin a b) where
  from_ = fromPreprocess >>= fromFinish

instance ( From a
         , From b
         ) => From (a, b) where
  from_ = (,) <$> from_ <*> from_

instance ( From a
         , From b
         , From c
         ) => From (a, b, c) where
  from_ = (,,) <$> from_ <*> from_ <*> from_

instance ( From a
         , From b
         , From c
         , From d
         ) => From (a, b, c, d) where
  from_ = (,,,) <$> from_ <*> from_ <*> from_ <*> from_

instance ( From a
         , From b
         , From c
         , From d
         , From e
         ) => From (a, b, c, d, e) where
  from_ = (,,,,) <$> from_ <*> from_ <*> from_ <*> from_ <*> from_

instance ( From a
         , From b
         , From c
         , From d
         , From e
         , From f
         ) => From (a, b, c, d, e, f) where
  from_ = (,,,,,) <$> from_ <*> from_ <*> from_ <*> from_ <*> from_ <*> from_

instance ( From a
         , From b
         , From c
         , From d
         , From e
         , From f
         , From g
         ) => From (a, b, c, d, e, f, g) where
  from_ = (,,,,,,) <$> from_ <*> from_ <*> from_ <*> from_ <*> from_ <*> from_ <*> from_

instance ( From a
         , From b
         , From c
         , From d
         , From e
         , From f
         , From g
         , From h
         ) => From (a, b, c, d, e, f, g, h) where
  from_ = (,,,,,,,) <$> from_ <*> from_ <*> from_ <*> from_ <*> from_ <*> from_ <*> from_ <*> from_



-- | (Internal) Class that implements the @JOIN@ 'from' magic
-- (see 'fromStart').
class FromPreprocess a where
  fromPreprocess :: SqlQuery (SqlExpr (PreprocessedFrom a))

instance ( PersistEntity val
         , BackendCompatible SqlBackend (PersistEntityBackend val)
         ) => FromPreprocess (SqlExpr (Entity val)) where
  fromPreprocess = fromStart

instance ( PersistEntity val
         , BackendCompatible SqlBackend (PersistEntityBackend val)
         ) => FromPreprocess (SqlExpr (Maybe (Entity val))) where
  fromPreprocess = fromStartMaybe

instance ( FromPreprocess a
         , FromPreprocess b
         , IsJoinKind join
         ) => FromPreprocess (join a b) where
  fromPreprocess = do
    a <- fromPreprocess
    b <- fromPreprocess
    fromJoin a b

-- | Exception data type for @esqueleto@ internal errors
data EsqueletoError =
    CompositeKeyErr CompositeKeyError
  | AliasedValueErr UnexpectedValueError
  | UnexpectedCaseErr UnexpectedCaseError
  | SqlBinOpCompositeErr SqlBinOpCompositeError
  deriving (Show)

instance Exception EsqueletoError

data UnexpectedValueError =
    NotError
  | ToInsertionError
  | CombineInsertionError
  | FoldHelpError
  | SqlCaseError
  | SqlCastAsError
  | MakeOnClauseError
  | MakeExcError
  | MakeSetError
  | MakeWhereError
  | MakeHavingError
  deriving (Show)

type CompositeKeyError = UnexpectedValueError

data UnexpectedCaseError =
    EmptySqlExprValueList
  | MakeFromError
  | UnsupportedSqlInsertIntoType
  | InsertionFinalError
  | NewIdentForError
  | UnsafeSqlCaseError
  | OperationNotSupported
  | NotImplemented
  deriving (Show)

data SqlBinOpCompositeError =
    MismatchingLengthsError
  | NullPlaceholdersError
  | DeconstructionError
  deriving (Show)



-- | SQL backend for @esqueleto@ using 'SqlPersistT'.
newtype SqlQuery a =
  Q { unQ :: W.WriterT SideData (S.State IdentState) a }

instance Functor SqlQuery where
  fmap f = Q . fmap f . unQ

instance Monad SqlQuery where
  return  = Q . return
  m >>= f = Q (unQ m >>= unQ . f)

instance Applicative SqlQuery where
  pure  = return
  (<*>) = ap


-- | Constraint synonym for @persistent@ entities whose backend
-- is 'SqlPersistT'.
type SqlEntity ent = (PersistEntity ent, PersistEntityBackend ent ~ SqlBackend)


----------------------------------------------------------------------


-- | Side data written by 'SqlQuery'.
data SideData = SideData { sdDistinctClause :: !DistinctClause
                         , sdFromClause     :: !FromClause
                         , sdSetClause      :: ![SetClause]
                         , sdWhereClause    :: !WhereClause
                         , sdGroupByClause  :: !GroupByClause
                         , sdHavingClause   :: !HavingClause
                         , sdOrderByClause  :: ![OrderByClause]
                         , sdLimitClause    :: !LimitClause
                         , sdLockingClause  :: !LockingClause
                         }

instance Semigroup SideData where
  SideData d f s w g h o l k <> SideData d' f' s' w' g' h' o' l' k' =
    SideData (d <> d') (f <> f') (s <> s') (w <> w') (g <> g') (h <> h') (o <> o') (l <> l') (k <> k')

instance Monoid SideData where
  mempty = SideData mempty mempty mempty mempty mempty mempty mempty mempty mempty
  mappend = (<>)

-- | The @DISTINCT@ "clause".
data DistinctClause =
    DistinctAll                     -- ^ The default, everything.
  | DistinctStandard                -- ^ Only @DISTINCT@, SQL standard.
  | DistinctOn [SqlExpr DistinctOn] -- ^ @DISTINCT ON@, PostgreSQL extension.

instance Semigroup DistinctClause where
  DistinctOn a     <> DistinctOn b = DistinctOn (a <> b)
  DistinctOn a     <> _            = DistinctOn a
  DistinctStandard <> _            = DistinctStandard
  DistinctAll      <> b            = b

instance Monoid DistinctClause where
  mempty = DistinctAll
  mappend = (<>)

-- | A part of a @FROM@ clause.
data FromClause =
    FromStart Ident EntityDef
  | FromJoin FromClause JoinKind FromClause (Maybe (SqlExpr (Value Bool)))
  | FromJoinPartial JoinKind FromClause
  | OnClause (SqlExpr (Value Bool))
  | FromQuery Ident (IdentInfo -> (TLB.Builder, [PersistValue]))
  | FromMany [FromClause]
  | FromNone


-- Make the semigroup version of FromClause look like the old list version
getFromClauseList :: FromClause -> [FromClause]
getFromClauseList (FromMany fs) = fs
getFromClauseList FromNone        = []
getFromClauseList f             = [f]

instance Semigroup FromClause where
  FromNone <> f = f
  f <> FromNone = f
  lhs@(FromJoin _ _ _ _) <> FromJoinPartial joinKind fromClause    = FromJoin lhs joinKind fromClause Nothing
  lhs@(FromStart _ _)    <> FromJoinPartial joinKind fromClause    = FromJoin lhs joinKind fromClause Nothing
  lhs@(FromQuery _ _)    <> FromJoinPartial joinKind fromClause    = FromJoin lhs joinKind fromClause Nothing
  f                      <> FromMany (f'@(FromJoinPartial _ _):fs) = FromMany ((f <> f') : fs)
  FromMany fs                         <> FromMany gs               = FromMany (fs <> gs)
  f                                   <> FromMany fs               = FromMany (f:fs)
  FromMany fs                         <> f                         = FromMany (fs ++ [f])
  f                                   <> f'                        = FromMany [f, f']

instance Monoid FromClause where
  mempty = FromNone
  mappend = (<>)

collectIdents :: FromClause -> Set Ident
collectIdents fc = case fc of
  FromStart i _ -> Set.singleton i
  FromJoin lhs _ rhs _ -> collectIdents lhs <> collectIdents rhs
  OnClause _ -> mempty
  FromQuery i _ -> Set.singleton i
  FromJoinPartial _ _ -> mempty
  FromMany _ -> mempty
  FromNone -> mempty

instance Show FromClause where
  show fc = case fc of
    FromStart i _ ->
      "(FromStart " <> show i <> ")"
    FromJoin lhs jk rhs mexpr ->
      mconcat
        [ "(FromJoin "
        , show lhs
        , " "
        , show jk
        , " "
        , case mexpr of
            Nothing -> "(no on clause)"
            Just expr -> "(" <> render' expr <> ")"
        , " "
        , show rhs
        , ")"
      ]
    OnClause expr ->
      "(OnClause " <> render' expr <> ")"
    FromQuery ident _->
      "(FromQuery " <> show ident <> ")"
    FromMany fs ->
      "(FromMany " <> show fs <> ")"
    FromNone ->
      "(FromNone)"
    FromJoinPartial jk f ->
      "(FromJoinPartial " <> show jk <> " " <> show f <> ")"

    where
      dummy = SqlBackend
        { connEscapeName = \(DBName x) -> x
        }
      render' = T.unpack . renderExpr dummy


-- | A part of a @SET@ clause.
newtype SetClause = SetClause (SqlExpr (Value ()))


-- | Collect 'OnClause's on 'FromJoin's.  Returns the first
-- unmatched 'OnClause's data on error.  Returns a list without
-- 'OnClauses' on success.
collectOnClauses
  :: SqlBackend
  -> [FromClause]
  -> Either (SqlExpr (Value Bool)) [FromClause]
collectOnClauses sqlBackend = go Set.empty []
  -- . (\fc -> Debug.trace ("From Clauses: " <> show fc) fc)
  where
    go is []  (f@(FromStart i _) : fs) =
      fmap (f:) (go (Set.insert i is) [] fs) -- fast path
    go is []  (f@(FromQuery i _) : fs) =
      fmap (f:) (go (Set.insert i is) [] fs) -- fast path
    go idents acc (OnClause expr : fs) = do
      (idents', a) <- findMatching idents acc expr
      go idents' a fs
    go idents acc (f:fs) =
      go idents (f:acc) fs
    go _ acc [] =
      return $ reverse acc

    findMatching
      :: Set Ident
      -> [FromClause]
      -> SqlExpr (Value Bool)
      -> Either (SqlExpr (Value Bool)) (Set Ident, [FromClause])
    findMatching idents fromClauses expr =
      -- Debug.trace ("From Clause: " <> show fromClauses) $
      case fromClauses of
        f : acc ->
          let
            idents' =
              idents
              <> Set.fromList (Maybe.catMaybes [findLeftmostIdent f, findRightmostIdent f])
          in
            case tryMatch idents' expr f of
              Just (idents'', f') ->
                return (idents'', f' : acc)
              Nothing ->
                fmap (f:) <$> findMatching idents' acc expr
        [] ->
          Left expr

    findRightmostIdent (FromStart i _) = Just i
    findRightmostIdent (FromQuery i _) = Just i
    findRightmostIdent (FromJoin _ _ r _) = findRightmostIdent r
    findRightmostIdent (FromJoinPartial _ _ ) = fail "wtf"
    findRightmostIdent (OnClause {}) = Nothing
    findRightmostIdent (FromNone) = Nothing
    findRightmostIdent (FromMany _) = Nothing

    findLeftmostIdent (FromStart i _) = Just i
    findLeftmostIdent (FromQuery i _) = Just i
    findLeftmostIdent (FromJoin l _ _ _) = findLeftmostIdent l
    findLeftmostIdent (FromJoinPartial _ _ ) = fail "wtf"
    findLeftmostIdent (OnClause {}) = Nothing
    findLeftmostIdent (FromNone) = Nothing
    findLeftmostIdent (FromMany _) = Nothing

    tryMatch
      :: Set Ident
      -> SqlExpr (Value Bool)
      -> FromClause
      -> Maybe (Set Ident, FromClause)
    tryMatch idents expr fromClause =
      case fromClause of
        FromJoin l k r onClause ->
          matchTable <|> matchR <|> matchC <|> matchL <|> matchPartial -- right to left
            where
              matchR = fmap (\r' -> FromJoin l k r' onClause)
                <$> tryMatch idents expr r
              matchL = fmap (\l' -> FromJoin l' k r onClause)
                <$> tryMatch idents expr l

              matchPartial = do
                --Debug.traceM $ "matchPartial"
                --Debug.traceM $ "matchPartial: identsInOnClause: " <> show identsInOnClause
                i1 <- findLeftmostIdent l
                i2 <- findLeftmostIdent r
                let leftIdents = collectIdents l
                -- Debug.traceM $ "matchPartial: i1: " <> show i1
                -- Debug.traceM $ "matchPartial: i2: " <> show i2
                -- Debug.traceM $ "matchPartial: idents: " <> show idents
                guard $
                  Set.isSubsetOf
                    identsInOnClause
                    (Set.fromList [i1, i2] <> leftIdents)
                guard $ k /= CrossJoinKind
                guard $ Maybe.isNothing onClause
                pure (idents, FromJoin l k r (Just expr))

              matchC =
                case onClause of
                  Nothing
                    | "?" `T.isInfixOf` renderedExpr ->
                        return (idents, FromJoin l k r (Just expr))
                    | Set.null identsInOnClause ->
                        return (idents, FromJoin l k r (Just expr))
                    | otherwise ->
                        Nothing
                  Just _ ->
                    Nothing
              matchTable = do
                i1 <- findLeftmostIdent r
                i2 <- findRightmostIdent l
                guard $ Set.fromList [i1, i2] `Set.isSubsetOf` identsInOnClause
                guard $ k /= CrossJoinKind
                guard $ Maybe.isNothing onClause
                pure (Set.fromList [i1, i2] <> idents, FromJoin l k r (Just expr))

        _ ->
          Nothing
      where
        identsInOnClause =
          onExprToTableIdentifiers

        renderedExpr =
          renderExpr sqlBackend expr

        onExprToTableIdentifiers =
          Set.map (I . tableAccessTable)
          . either error id
          . parseOnExpr sqlBackend
          $ renderedExpr

-- | A complete @WHERE@ clause.
data WhereClause = Where (SqlExpr (Value Bool))
                 | NoWhere

instance Semigroup WhereClause where
  NoWhere  <> w        = w
  w        <> NoWhere  = w
  Where e1 <> Where e2 = Where (e1 &&. e2)

instance Monoid WhereClause where
  mempty = NoWhere
  mappend = (<>)

-- | A @GROUP BY@ clause.
newtype GroupByClause = GroupBy [SomeValue]

instance Semigroup GroupByClause where
  GroupBy fs <> GroupBy fs' = GroupBy (fs <> fs')

instance Monoid GroupByClause where
  mempty = GroupBy []
  mappend = (<>)

-- | A @HAVING@ cause.
type HavingClause = WhereClause

-- | A @ORDER BY@ clause.
type OrderByClause = SqlExpr OrderBy


-- | A @LIMIT@ clause.
data LimitClause = Limit (Maybe Int64) (Maybe Int64)

instance Semigroup LimitClause where
  Limit l1 o1 <> Limit l2 o2 =
    Limit (l2 `mplus` l1) (o2 `mplus` o1)
    -- More than one 'limit' or 'offset' is issued, we want to
    -- keep the latest one.  That's why we use mplus with
    -- "reversed" arguments.

instance Monoid LimitClause where
  mempty = Limit mzero mzero
  mappend = (<>)

-- | A locking clause.
type LockingClause = Monoid.Last LockingKind


----------------------------------------------------------------------


-- | Identifier used for table names.
newtype Ident = I T.Text
  deriving (Eq, Ord, Show)


-- | List of identifiers already in use and supply of temporary
-- identifiers.
newtype IdentState = IdentState { inUse :: HS.HashSet T.Text }

initialIdentState :: IdentState
initialIdentState = IdentState mempty


-- | Create a fresh 'Ident'.  If possible, use the given
-- 'DBName'.
newIdentFor :: DBName -> SqlQuery Ident
newIdentFor (DBName original) = Q $ lift $ findFree Nothing
  where
    findFree msuffix = do
      let
        withSuffix =
          maybe id (\suffix -> (<> T.pack (show suffix))) msuffix original
      isInUse <- S.gets (HS.member withSuffix . inUse)
      if isInUse
        then findFree (succ <$> (msuffix <|> Just (1 :: Int)))
        else do
          S.modify (\s -> s { inUse = HS.insert withSuffix (inUse s) })
          pure (I withSuffix)

-- | Information needed to escape and use identifiers.
type IdentInfo = (SqlBackend, IdentState)


-- | Use an identifier.
useIdent :: IdentInfo -> Ident -> TLB.Builder
useIdent info (I ident) = fromDBName info $ DBName ident




-- | An expression on the SQL backend.
--
-- There are many comments describing the constructors of this
-- data type.  However, Haddock doesn't like GADTs, so you'll have to read them by hitting \"Source\".
data SqlExpr a where
  -- An entity, created by 'from' (cf. 'fromStart').
  EEntity  :: Ident -> SqlExpr (Entity val)
  --                Base     Table
  EAliasedEntity :: Ident -> Ident -> SqlExpr (Entity val)
  --                         Source   Base 
  EAliasedEntityReference :: Ident -> Ident -> SqlExpr (Entity val)

  -- Just a tag stating that something is nullable.
  EMaybe   :: SqlExpr a -> SqlExpr (Maybe a)

  -- Raw expression: states whether parenthesis are needed
  -- around this expression, and takes information about the SQL
  -- connection (mainly for escaping names) and returns both an
  -- string ('TLB.Builder') and a list of values to be
  -- interpolated by the SQL backend.
  ERaw     :: NeedParens -> (IdentInfo -> (TLB.Builder, [PersistValue])) -> SqlExpr (Value a)


  -- A raw expression with an alias 
  EAliasedValue :: Ident -> SqlExpr (Value a) -> SqlExpr (Value a)

  -- A reference to an aliased field in a table or subquery
  EValueReference :: Ident -> (IdentInfo -> Ident) -> SqlExpr (Value a)

  -- A composite key.
  --
  -- Persistent uses the same 'PersistList' constructor for both
  -- fields which are (homogeneous) lists of values and the
  -- (probably heterogeneous) values of a composite primary key.
  --
  -- We need to treat composite keys as fields.  For example, we
  -- have to support using ==., otherwise you wouldn't be able to
  -- join.  OTOH, lists of values should be treated exactly the
  -- same as any other scalar value.
  --
  -- In particular, this is valid for persistent via rawSql for
  -- an F field that is a list:
  --
  --   A.F in ?    -- [PersistList [foo, bar]]
  --
  -- However, this is not for a composite key entity:
  --
  --   A.ID = ?    -- [PersistList [foo, bar]]
  --
  -- The ID field doesn't exist on the DB for a composite key
  -- table, it exists only on the Haskell side.  Those variations
  -- also don't work:
  --
  --   (A.KeyA, A.KeyB) = ?    -- [PersistList [foo, bar]]
  --   [A.KeyA, A.KeyB] = ?    -- [PersistList [foo, bar]]
  --
  -- We have to generate:
  --
  --   A.KeyA = ? AND A.KeyB = ?      -- [foo, bar]
  --
  -- Note that the PersistList had to be deconstructed into its
  -- components.
  --
  -- In order to disambiguate behaviors, this constructor is used
  -- /only/ to represent a composite field access.  It does not
  -- represent a 'PersistList', not even if the 'PersistList' is
  -- used in the context of a composite key.  That's because it's
  -- impossible, e.g., for 'val' to disambiguate between these
  -- uses.
  ECompositeKey :: (IdentInfo -> [TLB.Builder]) -> SqlExpr (Value a)

  -- 'EList' and 'EEmptyList' are used by list operators.
  EList      :: SqlExpr (Value a) -> SqlExpr (ValueList a)
  EEmptyList :: SqlExpr (ValueList a)

  -- A 'SqlExpr' accepted only by 'orderBy'.
  EOrderBy :: OrderByType -> SqlExpr (Value a) -> SqlExpr OrderBy

  EOrderRandom :: SqlExpr OrderBy

  -- A 'SqlExpr' accepted only by 'distinctOn'.
  EDistinctOn :: SqlExpr (Value a) -> SqlExpr DistinctOn

  -- A 'SqlExpr' accepted only by 'set'.
  ESet :: (SqlExpr (Entity val) -> SqlExpr (Value ())) -> SqlExpr (Update val)

  -- An internal 'SqlExpr' used by the 'from' hack.
  EPreprocessedFrom :: a -> FromClause -> SqlExpr (PreprocessedFrom a)

  -- Used by 'insertSelect'.
  EInsert  :: Proxy a -> (IdentInfo -> (TLB.Builder, [PersistValue])) -> SqlExpr (Insertion a)
  EInsertFinal :: PersistEntity a => SqlExpr (Insertion a) -> SqlExpr InsertFinal

-- | Phantom type used to mark a @INSERT INTO@ query.
data InsertFinal

data NeedParens = Parens | Never

parensM :: NeedParens -> TLB.Builder -> TLB.Builder
parensM Never  = id
parensM Parens = parens

data OrderByType = ASC | DESC


instance ToSomeValues (SqlExpr (Value a)) where
  toSomeValues a = [SomeValue a]

fieldName :: (PersistEntity val, PersistField typ)
          => IdentInfo -> EntityField val typ -> TLB.Builder
fieldName info = fromDBName info . fieldDB . persistFieldDef

-- FIXME: Composite/non-id pKS not supported on set
setAux :: (PersistEntity val, PersistField typ)
       => EntityField val typ
       -> (SqlExpr (Entity val) -> SqlExpr (Value typ))
       -> SqlExpr (Update val)
setAux field mkVal = ESet $ \ent -> unsafeSqlBinOp " = " name (mkVal ent)
  where name = ERaw Never $ \info -> (fieldName info field, mempty)

sub :: PersistField a => Mode -> SqlQuery (SqlExpr (Value a)) -> SqlExpr (Value a)
sub mode query = ERaw Parens $ \info -> toRawSql mode info query

fromDBName :: IdentInfo -> DBName -> TLB.Builder
fromDBName (conn, _) = TLB.fromText . connEscapeName conn

existsHelper :: SqlQuery () -> SqlExpr (Value Bool)
existsHelper = sub SELECT . (>> return true)
  where
    true :: SqlExpr (Value Bool)
    true = val True

ifNotEmptyList :: SqlExpr (ValueList a) -> Bool -> SqlExpr (Value Bool) -> SqlExpr (Value Bool)
ifNotEmptyList EEmptyList b _ = val b
ifNotEmptyList (EList _)  _ x = x



----------------------------------------------------------------------


-- | (Internal) Create a case statement.
--
-- Since: 2.1.1
unsafeSqlCase :: PersistField a => [(SqlExpr (Value Bool), SqlExpr (Value a))] -> SqlExpr (Value a) -> SqlExpr (Value a)
unsafeSqlCase when v = ERaw Never buildCase
  where
    buildCase :: IdentInfo -> (TLB.Builder, [PersistValue])
    buildCase info =
      let (elseText, elseVals) = valueToSql v info
          (whenText, whenVals) = mapWhen when info
      in ( "CASE" <> whenText <> " ELSE " <> elseText <> " END", whenVals <> elseVals)

    mapWhen :: [(SqlExpr (Value Bool), SqlExpr (Value a))] -> IdentInfo -> (TLB.Builder, [PersistValue])
    mapWhen []    _    = throw (UnexpectedCaseErr UnsafeSqlCaseError)
    mapWhen when' info = foldl (foldHelp info) (mempty, mempty) when'

    foldHelp :: IdentInfo -> (TLB.Builder, [PersistValue]) -> (SqlExpr (Value Bool), SqlExpr (Value a)) -> (TLB.Builder, [PersistValue])
    foldHelp _ _ (ECompositeKey _, _) = throw (CompositeKeyErr FoldHelpError)
    foldHelp _ _ (_, ECompositeKey _) = throw (CompositeKeyErr FoldHelpError)
    foldHelp info (b0, vals0) (v1, v2) =
        let (b1, vals1) = valueToSql v1 info 
            (b2, vals2) = valueToSql v2 info
        in ( b0 <> " WHEN " <> b1 <> " THEN " <> b2, vals0 <> vals1 <> vals2 )

    valueToSql :: SqlExpr (Value a) -> IdentInfo -> (TLB.Builder, [PersistValue])
    valueToSql (ERaw p f) = (first (parensM p)) . f
    valueToSql (ECompositeKey _) = throw (CompositeKeyErr SqlCaseError)
    valueToSql (EAliasedValue i _) = aliasedValueIdentToRawSql i 
    valueToSql (EValueReference i i') = valueReferenceToRawSql i i'

-- | (Internal) Create a custom binary operator.  You /should/
-- /not/ use this function directly since its type is very
-- general, you should always use it with an explicit type
-- signature.  For example:
--
-- @
-- (==.) :: SqlExpr (Value a) -> SqlExpr (Value a) -> SqlExpr (Value Bool)
-- (==.) = unsafeSqlBinOp " = "
-- @
--
-- In the example above, we constraint the arguments to be of the
-- same type and constraint the result to be a boolean value.
unsafeSqlBinOp :: TLB.Builder -> SqlExpr (Value a) -> SqlExpr (Value b) -> SqlExpr (Value c)
unsafeSqlBinOp op (ERaw p1 f1) (ERaw p2 f2) = ERaw Parens f
  where
    f info = let (b1, vals1) = f1 info
                 (b2, vals2) = f2 info
             in ( parensM p1 b1 <> op <> parensM p2 b2
                , vals1 <> vals2 )
unsafeSqlBinOp op a b = unsafeSqlBinOp op (construct a) (construct b)
    where construct :: SqlExpr (Value a) -> SqlExpr (Value a)
          construct (ERaw p f)        = ERaw Parens $ \info ->
            let (b1, vals) = f info
                build ("?", [PersistList vals']) =
                  (uncommas $ replicate (length vals') "?", vals')
                build expr = expr
             in  build (parensM p b1, vals)
          construct (ECompositeKey f) =
            ERaw Parens $ \info -> (uncommas $ f info, mempty)
          construct (EAliasedValue i _) = 
            ERaw Never $ aliasedValueIdentToRawSql i
          construct (EValueReference i i') = 
            ERaw Never $ valueReferenceToRawSql i i' 
{-# INLINE unsafeSqlBinOp #-}




-- | Similar to 'unsafeSqlBinOp', but may also be applied to
-- composite keys.  Uses the operator given as the second
-- argument whenever applied to composite keys.
--
-- Usage example:
--
-- @
-- (==.) :: SqlExpr (Value a) -> SqlExpr (Value a) -> SqlExpr (Value Bool)
-- (==.) = unsafeSqlBinOpComposite " = " " AND "
-- @
--
-- Persistent has a hack for implementing composite keys (see
-- 'ECompositeKey' doc for more details), so we're forced to use
-- a hack here as well.  We deconstruct 'ERaw' values based on
-- two rules:
--
--   - If it is a single placeholder, then it's assumed to be
--   coming from a 'PersistList' and thus its components are
--   separated so that they may be applied to a composite key.
--
--   - If it is not a single placeholder, then it's assumed to be
--   a foreign (composite or not) key, so we enforce that it has
--   no placeholders and split it on the commas.
unsafeSqlBinOpComposite :: TLB.Builder -> TLB.Builder -> SqlExpr (Value a) -> SqlExpr (Value b) -> SqlExpr (Value c)
unsafeSqlBinOpComposite op _ a@(ERaw _ _) b@(ERaw _ _) = unsafeSqlBinOp op a b
unsafeSqlBinOpComposite op sep a b = ERaw Parens $ compose (listify a) (listify b)
  where
    listify :: SqlExpr (Value x) -> IdentInfo -> ([TLB.Builder], [PersistValue])
    listify (ECompositeKey f)      = flip (,) [] . f
    listify (ERaw _ f)             = deconstruct . f
    listify (EAliasedValue i _)    = deconstruct . (aliasedValueIdentToRawSql i)
    listify (EValueReference i i') = deconstruct . (valueReferenceToRawSql i i')

    deconstruct :: (TLB.Builder, [PersistValue]) -> ([TLB.Builder], [PersistValue])
    deconstruct ("?", [PersistList vals]) = (replicate (length vals) "?", vals)
    deconstruct (b', []) = (TLB.fromLazyText <$> TL.splitOn "," (TLB.toLazyText b'), [])
    deconstruct _ = throw (SqlBinOpCompositeErr DeconstructionError)

    compose f1 f2 info
      | not (null v1 || null v2) = throw (SqlBinOpCompositeErr NullPlaceholdersError)
      | length b1 /= length b2   = throw (SqlBinOpCompositeErr MismatchingLengthsError)
      | otherwise                = (bc, vc)
      where
        (b1, v1) = f1 info
        (b2, v2) = f2 info
        bc = intersperseB sep [x <> op <> y | (x, y) <- zip b1 b2]
        vc = v1 <> v2

-- | (Internal) A raw SQL value.  The same warning from
-- 'unsafeSqlBinOp' applies to this function as well.
unsafeSqlValue :: TLB.Builder -> SqlExpr (Value a)
unsafeSqlValue v = ERaw Never $ const (v, mempty)
{-# INLINE unsafeSqlValue #-}


-- | (Internal) A raw SQL function.  Once again, the same warning
-- from 'unsafeSqlBinOp' applies to this function as well.
unsafeSqlFunction :: UnsafeSqlFunctionArgument a =>
                     TLB.Builder -> a -> SqlExpr (Value b)
unsafeSqlFunction name arg =
  ERaw Never $ \info ->
    let (argsTLB, argsVals) =
          uncommas' $ map (\(ERaw _ f) -> f info) $ toArgList arg
    in (name <> parens argsTLB, argsVals)

-- | (Internal) An unsafe SQL function to extract a subfield from a compound
-- field, e.g. datetime. See 'unsafeSqlBinOp' for warnings.
--
-- Since: 1.3.6.
unsafeSqlExtractSubField :: UnsafeSqlFunctionArgument a =>
                     TLB.Builder -> a -> SqlExpr (Value b)
unsafeSqlExtractSubField subField arg =
  ERaw Never $ \info ->
    let (argsTLB, argsVals) =
          uncommas' $ map (\(ERaw _ f) -> f info) $ toArgList arg
    in ("EXTRACT" <> parens (subField <> " FROM " <> argsTLB), argsVals)

-- | (Internal) A raw SQL function. Preserves parentheses around arguments.
-- See 'unsafeSqlBinOp' for warnings.
unsafeSqlFunctionParens :: UnsafeSqlFunctionArgument a =>
                           TLB.Builder -> a -> SqlExpr (Value b)
unsafeSqlFunctionParens name arg =
  ERaw Never $ \info ->
    let (argsTLB, argsVals) =
          uncommas' $ map (\(ERaw p f) -> first (parensM p) (f info)) $ toArgList arg
    in (name <> parens argsTLB, argsVals)

-- | (Internal) An explicit SQL type cast using CAST(value as type).
-- See 'unsafeSqlBinOp' for warnings.
unsafeSqlCastAs :: T.Text -> SqlExpr (Value a) -> SqlExpr (Value b)
unsafeSqlCastAs t v = ERaw Never ((first (\value -> "CAST" <> parens (value <> " AS " <> TLB.fromText t))) . valueToText)
  where
    valueToText info =
      case v of
        (ERaw p f) ->
          let (b, vals) = f info
          in (parensM p b, vals)
        EAliasedValue i _ -> aliasedValueIdentToRawSql i info
        EValueReference i i' -> valueReferenceToRawSql i i' info
        ECompositeKey _ -> throw (CompositeKeyErr SqlCastAsError)
-- | (Internal) This class allows 'unsafeSqlFunction' to work with different
-- numbers of arguments; specifically it allows providing arguments to a sql
-- function via an n-tuple of @SqlExpr (Value _)@ values, which are not all
-- necessarily required to be the same type. There are instances for up to
-- 10-tuples, but for sql functions which take more than 10 arguments, you can
-- also nest tuples, as e.g. @toArgList ((a,b),(c,d))@ is the same as
-- @toArgList (a,b,c,d)@.
class UnsafeSqlFunctionArgument a where
  toArgList :: a -> [SqlExpr (Value ())]

-- | Useful for 0-argument functions, like @now@ in Postgresql.
--
-- @since 3.2.1
instance UnsafeSqlFunctionArgument () where
  toArgList _ = []

instance (a ~ Value b) => UnsafeSqlFunctionArgument (SqlExpr a) where
  toArgList = (:[]) . veryUnsafeCoerceSqlExprValue
instance UnsafeSqlFunctionArgument a =>
         UnsafeSqlFunctionArgument [a] where
  toArgList = concatMap toArgList
instance ( UnsafeSqlFunctionArgument a
         , UnsafeSqlFunctionArgument b
         ) => UnsafeSqlFunctionArgument (a, b) where
  toArgList (a, b) = toArgList a ++ toArgList b
instance ( UnsafeSqlFunctionArgument a
         , UnsafeSqlFunctionArgument b
         , UnsafeSqlFunctionArgument c
         ) => UnsafeSqlFunctionArgument (a, b, c) where
  toArgList = toArgList . from3
instance ( UnsafeSqlFunctionArgument a
         , UnsafeSqlFunctionArgument b
         , UnsafeSqlFunctionArgument c
         , UnsafeSqlFunctionArgument d
         ) => UnsafeSqlFunctionArgument (a, b, c, d) where
  toArgList = toArgList . from4
-- | @since 3.2.3
instance ( UnsafeSqlFunctionArgument a
         , UnsafeSqlFunctionArgument b
         , UnsafeSqlFunctionArgument c
         , UnsafeSqlFunctionArgument d
         , UnsafeSqlFunctionArgument e
         ) => UnsafeSqlFunctionArgument (a, b, c, d, e) where
  toArgList = toArgList . from5
-- | @since 3.2.3
instance ( UnsafeSqlFunctionArgument a
         , UnsafeSqlFunctionArgument b
         , UnsafeSqlFunctionArgument c
         , UnsafeSqlFunctionArgument d
         , UnsafeSqlFunctionArgument e
         , UnsafeSqlFunctionArgument f
         ) => UnsafeSqlFunctionArgument (a, b, c, d, e, f) where
  toArgList = toArgList . from6
-- | @since 3.2.3
instance ( UnsafeSqlFunctionArgument a
         , UnsafeSqlFunctionArgument b
         , UnsafeSqlFunctionArgument c
         , UnsafeSqlFunctionArgument d
         , UnsafeSqlFunctionArgument e
         , UnsafeSqlFunctionArgument f
         , UnsafeSqlFunctionArgument g
         ) => UnsafeSqlFunctionArgument (a, b, c, d, e, f, g) where
  toArgList = toArgList . from7
-- | @since 3.2.3
instance ( UnsafeSqlFunctionArgument a
         , UnsafeSqlFunctionArgument b
         , UnsafeSqlFunctionArgument c
         , UnsafeSqlFunctionArgument d
         , UnsafeSqlFunctionArgument e
         , UnsafeSqlFunctionArgument f
         , UnsafeSqlFunctionArgument g
         , UnsafeSqlFunctionArgument h
         ) => UnsafeSqlFunctionArgument (a, b, c, d, e, f, g, h) where
  toArgList = toArgList . from8
-- | @since 3.2.3
instance ( UnsafeSqlFunctionArgument a
         , UnsafeSqlFunctionArgument b
         , UnsafeSqlFunctionArgument c
         , UnsafeSqlFunctionArgument d
         , UnsafeSqlFunctionArgument e
         , UnsafeSqlFunctionArgument f
         , UnsafeSqlFunctionArgument g
         , UnsafeSqlFunctionArgument h
         , UnsafeSqlFunctionArgument i
         ) => UnsafeSqlFunctionArgument (a, b, c, d, e, f, g, h, i) where
  toArgList = toArgList . from9
-- | @since 3.2.3
instance ( UnsafeSqlFunctionArgument a
         , UnsafeSqlFunctionArgument b
         , UnsafeSqlFunctionArgument c
         , UnsafeSqlFunctionArgument d
         , UnsafeSqlFunctionArgument e
         , UnsafeSqlFunctionArgument f
         , UnsafeSqlFunctionArgument g
         , UnsafeSqlFunctionArgument h
         , UnsafeSqlFunctionArgument i
         , UnsafeSqlFunctionArgument j
         ) => UnsafeSqlFunctionArgument (a, b, c, d, e, f, g, h, i, j) where
  toArgList = toArgList . from10


-- | (Internal) Coerce a value's type from 'SqlExpr (Value a)' to
-- 'SqlExpr (Value b)'.  You should /not/ use this function
-- unless you know what you're doing!
veryUnsafeCoerceSqlExprValue :: SqlExpr (Value a) -> SqlExpr (Value b)
veryUnsafeCoerceSqlExprValue (ERaw p f)             = ERaw p f
veryUnsafeCoerceSqlExprValue (ECompositeKey f)      = ECompositeKey f
veryUnsafeCoerceSqlExprValue (EAliasedValue i v)    = EAliasedValue i (veryUnsafeCoerceSqlExprValue v)
veryUnsafeCoerceSqlExprValue (EValueReference i i') = EValueReference i i' 


-- | (Internal) Coerce a value's type from 'SqlExpr (ValueList
-- a)' to 'SqlExpr (Value a)'.  Does not work with empty lists.
veryUnsafeCoerceSqlExprValueList :: SqlExpr (ValueList a) -> SqlExpr (Value a)
veryUnsafeCoerceSqlExprValueList (EList v)  = v
veryUnsafeCoerceSqlExprValueList EEmptyList = throw (UnexpectedCaseErr EmptySqlExprValueList)


----------------------------------------------------------------------

-- | (Internal) Execute an @esqueleto@ @SELECT@ 'SqlQuery' inside
-- @persistent@'s 'SqlPersistT' monad.
rawSelectSource :: ( SqlSelect a r
                   , MonadIO m1
                   , MonadIO m2
                   )
                 => Mode
                 -> SqlQuery a
                 -> SqlReadT m1 (Acquire (C.ConduitT () r m2 ()))
rawSelectSource mode query =
      do
        conn <- projectBackend <$> R.ask
        let _ = conn :: SqlBackend
        res <- R.withReaderT (const conn) (run conn)
        return $ (C..| massage) `fmap` res
    where

      run conn =
        uncurry rawQueryRes $
        first builderToText $
        toRawSql mode (conn, initialIdentState) query

      massage = do
        mrow <- C.await
        case process <$> mrow of
          Just (Right r)  -> C.yield r >> massage
          Just (Left err) -> liftIO $ throwIO $ PersistMarshalError err
          Nothing         -> return ()

      process = sqlSelectProcessRow


-- | Execute an @esqueleto@ @SELECT@ query inside @persistent@'s
-- 'SqlPersistT' monad and return a 'C.Source' of rows.
selectSource :: ( SqlSelect a r
               , BackendCompatible SqlBackend backend
               , IsPersistBackend backend
               , PersistQueryRead backend
               , PersistStoreRead backend, PersistUniqueRead backend
               , MonadResource m )
             => SqlQuery a
             -> C.ConduitT () r (R.ReaderT backend m) ()
selectSource query = do
  res <- lift $ rawSelectSource SELECT query
  (key, src) <- lift $ allocateAcquire res
  src
  lift $ release key

-- | Execute an @esqueleto@ @SELECT@ query inside @persistent@'s
-- 'SqlPersistT' monad and return a list of rows.
--
-- We've seen that 'from' has some magic about which kinds of
-- things you may bring into scope.  This 'select' function also
-- has some magic for which kinds of things you may bring back to
-- Haskell-land by using @SqlQuery@'s @return@:
--
--  * You may return a @SqlExpr ('Entity' v)@ for an entity @v@
--  (i.e., like the @*@ in SQL), which is then returned to
--  Haskell-land as just @Entity v@.
--
--  * You may return a @SqlExpr (Maybe (Entity v))@ for an entity
--  @v@ that may be @NULL@, which is then returned to
--  Haskell-land as @Maybe (Entity v)@.  Used for @OUTER JOIN@s.
--
--  * You may return a @SqlExpr ('Value' t)@ for a value @t@
--  (i.e., a single column), where @t@ is any instance of
--  'PersistField', which is then returned to Haskell-land as
--  @Value t@.  You may use @Value@ to return projections of an
--  @Entity@ (see @('^.')@ and @('?.')@) or to return any other
--  value calculated on the query (e.g., 'countRows' or
--  'subSelect').
--
-- The @SqlSelect a r@ class has functional dependencies that
-- allow type information to flow both from @a@ to @r@ and
-- vice-versa.  This means that you'll almost never have to give
-- any type signatures for @esqueleto@ queries.  For example, the
-- query @'select' $ from $ \\p -> return p@ alone is ambiguous, but
-- in the context of
--
-- @
-- do ps <- 'select' $
--          'from' $ \\p ->
--          return p
--    liftIO $ mapM_ (putStrLn . personName . entityVal) ps
-- @
--
-- we are able to infer from that single @personName . entityVal@
-- function composition that the @p@ inside the query is of type
-- @SqlExpr (Entity Person)@.
select :: ( SqlSelect a r
          , MonadIO m
          )
       => SqlQuery a -> SqlReadT m [r]
select query = do
    res <- rawSelectSource SELECT query
    conn <- R.ask
    liftIO $ with res $ flip R.runReaderT conn . runSource

-- | (Internal) Run a 'C.Source' of rows.
runSource :: Monad m =>
             C.ConduitT () r (R.ReaderT backend m) ()
          -> R.ReaderT backend m [r]
runSource src = C.runConduit $ src C..| CL.consume


----------------------------------------------------------------------


-- | (Internal) Execute an @esqueleto@ statement inside
-- @persistent@'s 'SqlPersistT' monad.
rawEsqueleto :: ( MonadIO m, SqlSelect a r, BackendCompatible SqlBackend backend)
           => Mode
           -> SqlQuery a
           -> R.ReaderT backend m Int64
rawEsqueleto mode query = do
  conn <- R.ask
  uncurry rawExecuteCount $
    first builderToText $
    toRawSql mode (conn, initialIdentState) query


-- | Execute an @esqueleto@ @DELETE@ query inside @persistent@'s
-- 'SqlPersistT' monad.  Note that currently there are no type
-- checks for statements that should not appear on a @DELETE@
-- query.
--
-- Example of usage:
--
-- @
-- 'delete' $
-- 'from' $ \\appointment ->
-- 'where_' (appointment '^.' AppointmentDate '<.' 'val' now)
-- @
--
-- Unlike 'select', there is a useful way of using 'delete' that
-- will lead to type ambiguities.  If you want to delete all rows
-- (i.e., no 'where_' clause), you'll have to use a type signature:
--
-- @
-- 'delete' $
-- 'from' $ \\(appointment :: 'SqlExpr' ('Entity' Appointment)) ->
-- return ()
-- @
delete :: ( MonadIO m )
       => SqlQuery ()
       -> SqlWriteT m ()
delete = void . deleteCount

-- | Same as 'delete', but returns the number of rows affected.
deleteCount :: ( MonadIO m )
            => SqlQuery ()
            -> SqlWriteT m Int64
deleteCount = rawEsqueleto DELETE


-- | Execute an @esqueleto@ @UPDATE@ query inside @persistent@'s
-- 'SqlPersistT' monad.  Note that currently there are no type
-- checks for statements that should not appear on a @UPDATE@
-- query.
--
-- Example of usage:
--
-- @
-- 'update' $ \\p -> do
-- 'set' p [ PersonAge '=.' 'just' ('val' thisYear) -. p '^.' PersonBorn ]
-- 'where_' $ isNothing (p '^.' PersonAge)
-- @
update
  ::
  ( MonadIO m, PersistEntity val
  , BackendCompatible SqlBackend (PersistEntityBackend val)
  )
  => (SqlExpr (Entity val) -> SqlQuery ())
  -> SqlWriteT m ()
update = void . updateCount

-- | Same as 'update', but returns the number of rows affected.
updateCount
  ::
  ( MonadIO m, PersistEntity val
  , BackendCompatible SqlBackend (PersistEntityBackend val)
  )
  => (SqlExpr (Entity val) -> SqlQuery ())
  -> SqlWriteT m Int64
updateCount = rawEsqueleto UPDATE . from


----------------------------------------------------------------------


builderToText :: TLB.Builder -> T.Text
builderToText = TL.toStrict . TLB.toLazyTextWith defaultChunkSize
  where
    defaultChunkSize = 1024 - 32


-- | (Internal) Pretty prints a 'SqlQuery' into a SQL query.
--
-- Note: if you're curious about the SQL query being generated by
-- @esqueleto@, instead of manually using this function (which is
-- possible but tedious), see the 'renderQueryToText' function (along with
-- 'renderQuerySelect', 'renderQueryUpdate', etc).
toRawSql
  :: (SqlSelect a r, BackendCompatible SqlBackend backend)
  => Mode -> (backend, IdentState) -> SqlQuery a -> (TLB.Builder, [PersistValue])
toRawSql mode (conn, firstIdentState) query =
  let ((ret, sd), finalIdentState) =
        flip S.runState firstIdentState $
        W.runWriterT $
        unQ query
      SideData distinctClause
               fromClause
               setClauses
               whereClauses
               groupByClause
               havingClause
               orderByClauses
               limitClause
               lockingClause = sd
      -- Pass the finalIdentState (containing all identifiers
      -- that were used) to the subsequent calls.  This ensures
      -- that no name clashes will occur on subqueries that may
      -- appear on the expressions below.
      info = (projectBackend conn, finalIdentState)
  in mconcat
      [ makeInsertInto info mode ret
      , makeSelect     info mode distinctClause ret
      , makeFrom       info mode (getFromClauseList fromClause)
      , makeSet        info setClauses
      , makeWhere      info whereClauses
      , makeGroupBy    info groupByClause
      , makeHaving     info havingClause
      , makeOrderBy    info orderByClauses
      , makeLimit      info limitClause orderByClauses
      , makeLocking         lockingClause
      ]

-- | Renders a 'SqlQuery' into a 'Text' value along with the list of
-- 'PersistValue's that would be supplied to the database for @?@ placeholders.
--
-- You must ensure that the 'Mode' you pass to this function corresponds with
-- the actual 'SqlQuery'. If you pass a query that uses incompatible features
-- (like an @INSERT@ statement with a @SELECT@ mode) then you'll get a weird
-- result.
--
-- @since 3.1.1
renderQueryToText
  :: (SqlSelect a r, BackendCompatible SqlBackend backend, Monad m)
  => Mode
  -- ^ Whether to render as an 'SELECT', 'DELETE', etc.
  -> SqlQuery a
  -- ^ The SQL query you want to render.
  -> R.ReaderT backend m (T.Text, [PersistValue])
renderQueryToText mode query = do
  backend <- R.ask
  let (builder, pvals) = toRawSql mode (backend, initialIdentState) query
  pure (builderToText builder, pvals)

-- | Renders a 'SqlQuery' into a 'Text' value along with the list of
-- 'PersistValue's that would be supplied to the database for @?@ placeholders.
--
-- You must ensure that the 'Mode' you pass to this function corresponds with
-- the actual 'SqlQuery'. If you pass a query that uses incompatible features
-- (like an @INSERT@ statement with a @SELECT@ mode) then you'll get a weird
-- result.
--
-- @since 3.1.1
renderQuerySelect
  :: (SqlSelect a r, BackendCompatible SqlBackend backend, Monad m)
  => SqlQuery a
  -- ^ The SQL query you want to render.
  -> R.ReaderT backend m (T.Text, [PersistValue])
renderQuerySelect = renderQueryToText SELECT

-- | Renders a 'SqlQuery' into a 'Text' value along with the list of
-- 'PersistValue's that would be supplied to the database for @?@ placeholders.
--
-- You must ensure that the 'Mode' you pass to this function corresponds with
-- the actual 'SqlQuery'. If you pass a query that uses incompatible features
-- (like an @INSERT@ statement with a @SELECT@ mode) then you'll get a weird
-- result.
--
-- @since 3.1.1
renderQueryDelete
  :: (SqlSelect a r, BackendCompatible SqlBackend backend, Monad m)
  => SqlQuery a
  -- ^ The SQL query you want to render.
  -> R.ReaderT backend m (T.Text, [PersistValue])
renderQueryDelete = renderQueryToText DELETE

-- | Renders a 'SqlQuery' into a 'Text' value along with the list of
-- 'PersistValue's that would be supplied to the database for @?@ placeholders.
--
-- You must ensure that the 'Mode' you pass to this function corresponds with
-- the actual 'SqlQuery'. If you pass a query that uses incompatible features
-- (like an @INSERT@ statement with a @SELECT@ mode) then you'll get a weird
-- result.
--
-- @since 3.1.1
renderQueryUpdate
  :: (SqlSelect a r, BackendCompatible SqlBackend backend, Monad m)
  => SqlQuery a
  -- ^ The SQL query you want to render.
  -> R.ReaderT backend m (T.Text, [PersistValue])
renderQueryUpdate = renderQueryToText UPDATE

-- | Renders a 'SqlQuery' into a 'Text' value along with the list of
-- 'PersistValue's that would be supplied to the database for @?@ placeholders.
--
-- You must ensure that the 'Mode' you pass to this function corresponds with
-- the actual 'SqlQuery'. If you pass a query that uses incompatible features
-- (like an @INSERT@ statement with a @SELECT@ mode) then you'll get a weird
-- result.
--
-- @since 3.1.1
renderQueryInsertInto
  :: (SqlSelect a r, BackendCompatible SqlBackend backend, Monad m)
  => SqlQuery a
  -- ^ The SQL query you want to render.
  -> R.ReaderT backend m (T.Text, [PersistValue])
renderQueryInsertInto = renderQueryToText INSERT_INTO

-- | (Internal) Mode of query being converted by 'toRawSql'.
data Mode =
    SELECT
  | DELETE
  | UPDATE
  | INSERT_INTO


uncommas :: [TLB.Builder] -> TLB.Builder
uncommas = intersperseB ", "

intersperseB :: TLB.Builder -> [TLB.Builder] -> TLB.Builder
intersperseB a = mconcat . intersperse a . filter (/= mempty)

uncommas' :: Monoid a => [(TLB.Builder, a)] -> (TLB.Builder, a)
uncommas' = (uncommas *** mconcat) . unzip


makeInsertInto :: SqlSelect a r => IdentInfo -> Mode -> a -> (TLB.Builder, [PersistValue])
makeInsertInto info INSERT_INTO ret = sqlInsertInto info ret
makeInsertInto _    _           _   = mempty


makeSelect :: SqlSelect a r => IdentInfo -> Mode -> DistinctClause -> a -> (TLB.Builder, [PersistValue])
makeSelect info mode_ distinctClause ret = process mode_
  where
    process mode =
      case mode of
        SELECT      -> withCols selectKind
        DELETE      -> plain "DELETE "
        UPDATE      -> plain "UPDATE "
        INSERT_INTO -> process SELECT
    selectKind =
      case distinctClause of
        DistinctAll      -> ("SELECT ", [])
        DistinctStandard -> ("SELECT DISTINCT ", [])
        DistinctOn exprs -> first (("SELECT DISTINCT ON (" <>) . (<> ") ")) $
                            uncommas' (processExpr <$> exprs)
      where processExpr (EDistinctOn f) = materializeExpr info f
    withCols v = v <> sqlSelectCols info ret
    plain    v = (v, [])


makeFrom
  :: IdentInfo
  -> Mode
  -> [FromClause]
  -> (TLB.Builder, [PersistValue])
makeFrom _    _    [] = mempty
makeFrom info mode fs = ret
  where
    ret = case collectOnClauses (fst info) fs of
            Left expr -> throw $ mkExc expr
            Right fs' -> keyword $ uncommas' (map (mk Never) fs')
    keyword = case mode of
                UPDATE -> id
                _      -> first ("\nFROM " <>)

    mk _     (FromStart i def) = base i def
    mk paren (FromJoin lhs kind rhs monClause) =
      first (parensM paren) $
      mconcat [ mk Never lhs
              , (fromKind kind, mempty)
              , mk Parens rhs
              , maybe mempty makeOnClause monClause
              ]
    mk _ (FromQuery ident f) = 
      let (queryText, queryVals) = f info
      in ((parens queryText) <> " AS " <> useIdent info ident, queryVals)

    mk _ (OnClause _)          = throw (UnexpectedCaseErr MakeFromError)
    mk _ (FromNone  )          = throw (UnexpectedCaseErr MakeFromError)
    mk _ (FromMany _)          = throw (UnexpectedCaseErr MakeFromError)
    mk _ (FromJoinPartial _ _) = throw (UnexpectedCaseErr MakeFromError)

    base ident@(I identText) def =
      let db@(DBName dbText) = entityDB def
      in ( if dbText == identText
           then fromDBName info db
           else fromDBName info db <> (" AS " <> useIdent info ident)
         , mempty )

    fromKind InnerJoinKind      = " INNER JOIN "
    fromKind CrossJoinKind      = " CROSS JOIN "
    fromKind LeftOuterJoinKind  = " LEFT OUTER JOIN "
    fromKind RightOuterJoinKind = " RIGHT OUTER JOIN "
    fromKind FullOuterJoinKind  = " FULL OUTER JOIN "

    makeOnClause (ERaw _ f)        = first (" ON " <>) (f info)
    makeOnClause (ECompositeKey _) = throw (CompositeKeyErr MakeOnClauseError)
    makeOnClause (EAliasedValue _ _) = throw (AliasedValueErr MakeOnClauseError)
    makeOnClause (EValueReference _ _) = throw (AliasedValueErr MakeOnClauseError)

    mkExc :: SqlExpr (Value Bool) -> OnClauseWithoutMatchingJoinException
    mkExc (ERaw _ f) =
      OnClauseWithoutMatchingJoinException $
      TL.unpack $ TLB.toLazyText $ fst (f info)
    mkExc (ECompositeKey _) = throw (CompositeKeyErr MakeExcError)
    mkExc (EAliasedValue _ _) = throw (AliasedValueErr MakeExcError)
    mkExc (EValueReference _ _) = throw (AliasedValueErr MakeExcError)

makeSet :: IdentInfo -> [SetClause] -> (TLB.Builder, [PersistValue])
makeSet _    [] = mempty
makeSet info os = first ("\nSET " <>) . uncommas' $ concatMap mk os
  where
    mk (SetClause (ERaw _ f))             = [f info]
    mk (SetClause (ECompositeKey _))      = throw (CompositeKeyErr MakeSetError) -- FIXME
    mk (SetClause (EAliasedValue i _))    = [aliasedValueIdentToRawSql i info]
    mk (SetClause (EValueReference i i')) = [valueReferenceToRawSql i i' info]

makeWhere :: IdentInfo -> WhereClause -> (TLB.Builder, [PersistValue])
makeWhere _    NoWhere                       = mempty
makeWhere info (Where v) = first ("\nWHERE " <>) $ x info
  where
    x =
      case v of 
        ERaw _ f             -> f
        EAliasedValue i _    -> aliasedValueIdentToRawSql i
        EValueReference i i' -> valueReferenceToRawSql i i'
        ECompositeKey _      -> throw (CompositeKeyErr MakeWhereError)

makeGroupBy :: IdentInfo -> GroupByClause -> (TLB.Builder, [PersistValue])
makeGroupBy _ (GroupBy []) = (mempty, [])
makeGroupBy info (GroupBy fields) = first ("\nGROUP BY " <>) build
  where
    build :: (TLB.Builder, [PersistValue])
    build = uncommas' $ map match fields

    match :: SomeValue -> (TLB.Builder, [PersistValue])
    match (SomeValue (ERaw _ f)) = f info
    match (SomeValue (ECompositeKey f)) = (mconcat $ f info, mempty)
    match (SomeValue (EAliasedValue i _)) = aliasedValueIdentToRawSql i info
    match (SomeValue (EValueReference i i')) = valueReferenceToRawSql i i' info

makeHaving :: IdentInfo -> WhereClause -> (TLB.Builder, [PersistValue])
makeHaving _    NoWhere   = mempty
makeHaving info (Where v) = first ("\nHAVING " <>) $ x info
  where
    x =
      case v of 
        ERaw _ f             -> f
        EAliasedValue i _    -> aliasedValueIdentToRawSql i
        EValueReference i i' -> valueReferenceToRawSql i i'
        ECompositeKey _      -> throw (CompositeKeyErr MakeHavingError)

-- makeHaving, makeWhere and makeOrderBy
makeOrderByNoNewline ::
     IdentInfo -> [OrderByClause] -> (TLB.Builder, [PersistValue])
makeOrderByNoNewline _    [] = mempty
makeOrderByNoNewline info os = first ("ORDER BY " <>) . uncommas' $ concatMap mk os
  where
    mk :: OrderByClause -> [(TLB.Builder, [PersistValue])]
    mk (EOrderBy t (ECompositeKey f)) =
      let fs = f info
          vals = repeat []
      in zip (map (<> orderByType t) fs) vals
    mk (EOrderBy t v) = 
      let x = case v of
                ERaw p f -> (first (parensM p)) . f
                EAliasedValue i _ -> aliasedValueIdentToRawSql i 
                EValueReference i i' -> valueReferenceToRawSql i i' 
                ECompositeKey _ -> undefined -- defined above
      in [ first (<> orderByType t) $ x info ]
    mk EOrderRandom = [first (<> "RANDOM()") mempty]

    orderByType ASC  = " ASC"
    orderByType DESC = " DESC"

makeOrderBy :: IdentInfo -> [OrderByClause] -> (TLB.Builder, [PersistValue])
makeOrderBy _ [] = mempty
makeOrderBy info is =
  let (tlb, vals) = makeOrderByNoNewline info is
  in ("\n" <> tlb, vals)

{-# DEPRECATED EOrderRandom "Since 2.6.0: `rand` ordering function is not uniform across all databases! To avoid accidental partiality it will be removed in the next major version." #-}

makeLimit :: IdentInfo -> LimitClause -> [OrderByClause] -> (TLB.Builder, [PersistValue])
makeLimit (conn, _) (Limit ml mo) orderByClauses =
  let limitRaw = connLimitOffset conn (v ml, v mo) hasOrderClause "\n"
      hasOrderClause = not (null orderByClauses)
      v = maybe 0 fromIntegral
  in (TLB.fromText limitRaw, mempty)


makeLocking :: LockingClause -> (TLB.Builder, [PersistValue])
makeLocking = flip (,) [] . maybe mempty toTLB . Monoid.getLast
  where
    toTLB ForUpdate           = "\nFOR UPDATE"
    toTLB ForUpdateSkipLocked = "\nFOR UPDATE SKIP LOCKED"
    toTLB ForShare            = "\nFOR SHARE"
    toTLB LockInShareMode     = "\nLOCK IN SHARE MODE"



parens :: TLB.Builder -> TLB.Builder
parens b = "(" <> (b <> ")")

aliasedValueIdentToRawSql :: Ident -> IdentInfo -> (TLB.Builder, [PersistValue])
aliasedValueIdentToRawSql i info =
  (useIdent info i, mempty)

valueReferenceToRawSql ::  Ident -> (IdentInfo -> Ident) -> IdentInfo -> (TLB.Builder, [PersistValue])
valueReferenceToRawSql sourceIdent columnIdentF info =
  (useIdent info sourceIdent <> "." <> useIdent info (columnIdentF info), mempty)

aliasedEntityColumnIdent :: Ident -> FieldDef -> IdentInfo -> Ident
aliasedEntityColumnIdent (I baseIdent) field info =
  I (baseIdent <> "_" <> (builderToText $ fromDBName info $ fieldDB field))

aliasedColumnName :: Ident -> IdentInfo -> T.Text -> TLB.Builder 
aliasedColumnName (I baseIdent) info columnName = 
  useIdent info (I (baseIdent <> "_" <> columnName))

----------------------------------------------------------------------


-- | (Internal) Class for mapping results coming from 'SqlQuery'
-- into actual results.
--
-- This looks very similar to @RawSql@, and it is!  However,
-- there are some crucial differences and ultimately they're
-- different classes.
class SqlSelect a r | a -> r, r -> a where
  -- | Creates the variable part of the @SELECT@ query and
  -- returns the list of 'PersistValue's that will be given to
  -- 'rawQuery'.
  sqlSelectCols :: IdentInfo -> a -> (TLB.Builder, [PersistValue])

  -- | Number of columns that will be consumed.
  sqlSelectColCount :: Proxy a -> Int

  -- | Transform a row of the result into the data type.
  sqlSelectProcessRow :: [PersistValue] -> Either T.Text r

  -- | Create @INSERT INTO@ clause instead.
  sqlInsertInto :: IdentInfo -> a -> (TLB.Builder, [PersistValue])
  sqlInsertInto = throw (UnexpectedCaseErr UnsupportedSqlInsertIntoType)


-- | @INSERT INTO@ hack.
instance SqlSelect (SqlExpr InsertFinal) InsertFinal where
  sqlInsertInto info (EInsertFinal (EInsert p _)) =
    let fields = uncommas $
                 map (fromDBName info . fieldDB) $
                 entityFields $
                 entityDef p
        table  = fromDBName info . entityDB . entityDef $ p
    in ("INSERT INTO " <> table <> parens fields <> "\n", [])
  sqlSelectCols info (EInsertFinal (EInsert _ f)) = f info
  sqlSelectColCount   = const 0
  sqlSelectProcessRow =
    const (Right (throw (UnexpectedCaseErr InsertionFinalError)))


-- | Not useful for 'select', but used for 'update' and 'delete'.
instance SqlSelect () () where
  sqlSelectCols _ _ = ("1", [])
  sqlSelectColCount _ = 1
  sqlSelectProcessRow _ = Right ()


-- | You may return an 'Entity' from a 'select' query.
instance PersistEntity a => SqlSelect (SqlExpr (Entity a)) (Entity a) where
  sqlSelectCols info expr@(EEntity ident) = ret
      where
        process ed = uncommas $
                     map ((name <>) . TLB.fromText) $
                     entityColumnNames ed (fst info)
        -- 'name' is the biggest difference between 'RawSql' and
        -- 'SqlSelect'.  We automatically create names for tables
        -- (since it's not the user who's writing the FROM
        -- clause), while 'rawSql' assumes that it's just the
        -- name of the table (which doesn't allow self-joins, for
        -- example).
        name = useIdent info ident <> "."
        ret = let ed = entityDef $ getEntityVal $ return expr
              in (process ed, mempty)
  sqlSelectCols info expr@(EAliasedEntity aliasIdent tableIdent) = ret
      where
        process ed = uncommas $
                     map ((name <>) . aliasName) $
                     entityColumnNames ed (fst info)
        aliasName columnName = (TLB.fromText columnName) <> " AS " <> aliasedColumnName aliasIdent info columnName 
        name = useIdent info tableIdent <> "."
        ret = let ed = entityDef $ getEntityVal $ return expr
              in (process ed, mempty)
  sqlSelectCols info expr@(EAliasedEntityReference sourceIdent baseIdent) = ret
      where
        process ed = uncommas $
                     map ((name <>) . aliasedColumnName baseIdent info) $
                     entityColumnNames ed (fst info)
        name = useIdent info sourceIdent <> "."
        ret = let ed = entityDef $ getEntityVal $ return expr
              in (process ed, mempty)
  sqlSelectColCount = entityColumnCount . entityDef . getEntityVal
  sqlSelectProcessRow = parseEntityValues ed
    where ed = entityDef $ getEntityVal (Proxy :: Proxy (SqlExpr (Entity a)))


getEntityVal :: Proxy (SqlExpr (Entity a)) -> Proxy a
getEntityVal = const Proxy


-- | You may return a possibly-@NULL@ 'Entity' from a 'select' query.
instance PersistEntity a => SqlSelect (SqlExpr (Maybe (Entity a))) (Maybe (Entity a)) where
  sqlSelectCols info (EMaybe ent) = sqlSelectCols info ent
  sqlSelectColCount = sqlSelectColCount . fromEMaybe
    where
      fromEMaybe :: Proxy (SqlExpr (Maybe e)) -> Proxy (SqlExpr e)
      fromEMaybe = const Proxy
  sqlSelectProcessRow cols
    | all (== PersistNull) cols = return Nothing
    | otherwise                 = Just <$> sqlSelectProcessRow cols


-- | You may return any single value (i.e. a single column) from
-- a 'select' query.
instance PersistField a => SqlSelect (SqlExpr (Value a)) (Value a) where
  sqlSelectCols = materializeExpr
  sqlSelectColCount = const 1
  sqlSelectProcessRow [pv] = Value <$> fromPersistValue pv
  sqlSelectProcessRow pvs  = Value <$> fromPersistValue (PersistList pvs)

-- | Materialize a @SqlExpr (Value a)@.
materializeExpr :: IdentInfo -> SqlExpr (Value a) -> (TLB.Builder, [PersistValue])
materializeExpr info (ERaw p f) =
  let (b, vals) = f info
  in (parensM p b, vals)
materializeExpr info (ECompositeKey f) =
  let bs = f info
  in (uncommas $ map (parensM Parens) bs, [])
materializeExpr info (EAliasedValue ident x) =
  let (b, vals) = materializeExpr info x
  in (b <> " AS " <> (useIdent info ident), vals)
materializeExpr info (EValueReference sourceIdent columnIdent) =
  valueReferenceToRawSql sourceIdent columnIdent info

-- | You may return tuples (up to 16-tuples) and tuples of tuples
-- from a 'select' query.
instance ( SqlSelect a ra
         , SqlSelect b rb
         ) => SqlSelect (a, b) (ra, rb) where
  sqlSelectCols esc (a, b) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      ]
  sqlSelectColCount = uncurry (+) . (sqlSelectColCount *** sqlSelectColCount) . fromTuple
    where
      fromTuple :: Proxy (a,b) -> (Proxy a, Proxy b)
      fromTuple = const (Proxy, Proxy)
  sqlSelectProcessRow =
    let x = getType processRow
        getType :: SqlSelect a r => (z -> Either y (r,x)) -> Proxy a
        getType = const Proxy

        colCountFst = sqlSelectColCount x

        processRow row =
            let (rowFst, rowSnd) = splitAt colCountFst row
            in (,) <$> sqlSelectProcessRow rowFst
                   <*> sqlSelectProcessRow rowSnd

    in colCountFst `seq` processRow
       -- Avoids recalculating 'colCountFst'.


instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         ) => SqlSelect (a, b, c) (ra, rb, rc) where
  sqlSelectCols esc (a, b, c) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      ]
  sqlSelectColCount   = sqlSelectColCount . from3P
  sqlSelectProcessRow = fmap to3 . sqlSelectProcessRow

from3P :: Proxy (a,b,c) -> Proxy ((a,b),c)
from3P = const Proxy

from3 :: (a,b,c) -> ((a,b),c)
from3 (a,b,c) = ((a,b),c)

to3 :: ((a,b),c) -> (a,b,c)
to3 ((a,b),c) = (a,b,c)


instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         ) => SqlSelect (a, b, c, d) (ra, rb, rc, rd) where
  sqlSelectCols esc (a, b, c, d) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      ]
  sqlSelectColCount   = sqlSelectColCount . from4P
  sqlSelectProcessRow = fmap to4 . sqlSelectProcessRow

from4P :: Proxy (a,b,c,d) -> Proxy ((a,b),(c,d))
from4P = const Proxy

from4 :: (a,b,c,d) -> ((a,b),(c,d))
from4 (a,b,c,d) = ((a,b),(c,d))

to4 :: ((a,b),(c,d)) -> (a,b,c,d)
to4 ((a,b),(c,d)) = (a,b,c,d)


instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         ) => SqlSelect (a, b, c, d, e) (ra, rb, rc, rd, re) where
  sqlSelectCols esc (a, b, c, d, e) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      ]
  sqlSelectColCount   = sqlSelectColCount . from5P
  sqlSelectProcessRow = fmap to5 . sqlSelectProcessRow

from5P :: Proxy (a,b,c,d,e) -> Proxy ((a,b),(c,d),e)
from5P = const Proxy

from5 :: (a,b,c,d,e) -> ((a,b),(c,d),e)
from5 (a,b,c,d,e) = ((a,b),(c,d),e)

to5 :: ((a,b),(c,d),e) -> (a,b,c,d,e)
to5 ((a,b),(c,d),e) = (a,b,c,d,e)


instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         ) => SqlSelect (a, b, c, d, e, f) (ra, rb, rc, rd, re, rf) where
  sqlSelectCols esc (a, b, c, d, e, f) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      ]
  sqlSelectColCount   = sqlSelectColCount . from6P
  sqlSelectProcessRow = fmap to6 . sqlSelectProcessRow

from6P :: Proxy (a,b,c,d,e,f) -> Proxy ((a,b),(c,d),(e,f))
from6P = const Proxy

from6 :: (a,b,c,d,e,f) -> ((a,b),(c,d),(e,f))
from6 (a,b,c,d,e,f) = ((a,b),(c,d),(e,f))

to6 :: ((a,b),(c,d),(e,f)) -> (a,b,c,d,e,f)
to6 ((a,b),(c,d),(e,f)) = (a,b,c,d,e,f)


instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         ) => SqlSelect (a, b, c, d, e, f, g) (ra, rb, rc, rd, re, rf, rg) where
  sqlSelectCols esc (a, b, c, d, e, f, g) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      ]
  sqlSelectColCount   = sqlSelectColCount . from7P
  sqlSelectProcessRow = fmap to7 . sqlSelectProcessRow

from7P :: Proxy (a,b,c,d,e,f,g) -> Proxy ((a,b),(c,d),(e,f),g)
from7P = const Proxy

from7 :: (a,b,c,d,e,f,g) -> ((a,b),(c,d),(e,f),g)
from7 (a,b,c,d,e,f,g) = ((a,b),(c,d),(e,f),g)

to7 :: ((a,b),(c,d),(e,f),g) -> (a,b,c,d,e,f,g)
to7 ((a,b),(c,d),(e,f),g) = (a,b,c,d,e,f,g)


instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         , SqlSelect h rh
         ) => SqlSelect (a, b, c, d, e, f, g, h) (ra, rb, rc, rd, re, rf, rg, rh) where
  sqlSelectCols esc (a, b, c, d, e, f, g, h) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      , sqlSelectCols esc h
      ]
  sqlSelectColCount   = sqlSelectColCount . from8P
  sqlSelectProcessRow = fmap to8 . sqlSelectProcessRow

from8P :: Proxy (a,b,c,d,e,f,g,h) -> Proxy ((a,b),(c,d),(e,f),(g,h))
from8P = const Proxy

from8 :: (a,b,c,d,e,f,g,h) -> ((a,b),(c,d),(e,f),(g,h))
from8 (a,b,c,d,e,f,g,h) = ((a,b),(c,d),(e,f),(g,h))

to8 :: ((a,b),(c,d),(e,f),(g,h)) -> (a,b,c,d,e,f,g,h)
to8 ((a,b),(c,d),(e,f),(g,h)) = (a,b,c,d,e,f,g,h)

instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         , SqlSelect h rh
         , SqlSelect i ri
         ) => SqlSelect (a, b, c, d, e, f, g, h, i) (ra, rb, rc, rd, re, rf, rg, rh, ri) where
  sqlSelectCols esc (a, b, c, d, e, f, g, h, i) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      , sqlSelectCols esc h
      , sqlSelectCols esc i
      ]
  sqlSelectColCount   = sqlSelectColCount . from9P
  sqlSelectProcessRow = fmap to9 . sqlSelectProcessRow

from9P :: Proxy (a,b,c,d,e,f,g,h,i) -> Proxy ((a,b),(c,d),(e,f),(g,h),i)
from9P = const Proxy

from9 :: (a,b,c,d,e,f,g,h,i) -> ((a,b),(c,d),(e,f),(g,h),i)
from9 (a,b,c,d,e,f,g,h,i) = ((a,b),(c,d),(e,f),(g,h),i)

to9 :: ((a,b),(c,d),(e,f),(g,h),i) -> (a,b,c,d,e,f,g,h,i)
to9 ((a,b),(c,d),(e,f),(g,h),i) = (a,b,c,d,e,f,g,h,i)

instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         , SqlSelect h rh
         , SqlSelect i ri
         , SqlSelect j rj
         ) => SqlSelect (a, b, c, d, e, f, g, h, i, j) (ra, rb, rc, rd, re, rf, rg, rh, ri, rj) where
  sqlSelectCols esc (a, b, c, d, e, f, g, h, i, j) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      , sqlSelectCols esc h
      , sqlSelectCols esc i
      , sqlSelectCols esc j
      ]
  sqlSelectColCount   = sqlSelectColCount . from10P
  sqlSelectProcessRow = fmap to10 . sqlSelectProcessRow

from10P :: Proxy (a,b,c,d,e,f,g,h,i,j) -> Proxy ((a,b),(c,d),(e,f),(g,h),(i,j))
from10P = const Proxy

from10 :: (a,b,c,d,e,f,g,h,i,j) -> ((a,b),(c,d),(e,f),(g,h),(i,j))
from10 (a,b,c,d,e,f,g,h,i,j) = ((a,b),(c,d),(e,f),(g,h),(i,j))

to10 :: ((a,b),(c,d),(e,f),(g,h),(i,j)) -> (a,b,c,d,e,f,g,h,i,j)
to10 ((a,b),(c,d),(e,f),(g,h),(i,j)) = (a,b,c,d,e,f,g,h,i,j)


instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         , SqlSelect h rh
         , SqlSelect i ri
         , SqlSelect j rj
         , SqlSelect k rk
         ) => SqlSelect (a, b, c, d, e, f, g, h, i, j, k) (ra, rb, rc, rd, re, rf, rg, rh, ri, rj, rk) where
  sqlSelectCols esc (a, b, c, d, e, f, g, h, i, j, k) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      , sqlSelectCols esc h
      , sqlSelectCols esc i
      , sqlSelectCols esc j
      , sqlSelectCols esc k
      ]
  sqlSelectColCount   = sqlSelectColCount . from11P
  sqlSelectProcessRow = fmap to11 . sqlSelectProcessRow

from11P :: Proxy (a,b,c,d,e,f,g,h,i,j,k) -> Proxy ((a,b),(c,d),(e,f),(g,h),(i,j),k)
from11P = const Proxy

to11 :: ((a,b),(c,d),(e,f),(g,h),(i,j),k) -> (a,b,c,d,e,f,g,h,i,j,k)
to11 ((a,b),(c,d),(e,f),(g,h),(i,j),k) = (a,b,c,d,e,f,g,h,i,j,k)

instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         , SqlSelect h rh
         , SqlSelect i ri
         , SqlSelect j rj
         , SqlSelect k rk
         , SqlSelect l rl
         ) => SqlSelect (a, b, c, d, e, f, g, h, i, j, k, l) (ra, rb, rc, rd, re, rf, rg, rh, ri, rj, rk, rl) where
  sqlSelectCols esc (a, b, c, d, e, f, g, h, i, j, k, l) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      , sqlSelectCols esc h
      , sqlSelectCols esc i
      , sqlSelectCols esc j
      , sqlSelectCols esc k
      , sqlSelectCols esc l
      ]
  sqlSelectColCount   = sqlSelectColCount . from12P
  sqlSelectProcessRow = fmap to12 . sqlSelectProcessRow

from12P :: Proxy (a,b,c,d,e,f,g,h,i,j,k,l) -> Proxy ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l))
from12P = const Proxy

to12 :: ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l)) -> (a,b,c,d,e,f,g,h,i,j,k,l)
to12 ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l)) = (a,b,c,d,e,f,g,h,i,j,k,l)

instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         , SqlSelect h rh
         , SqlSelect i ri
         , SqlSelect j rj
         , SqlSelect k rk
         , SqlSelect l rl
         , SqlSelect m rm
         ) => SqlSelect (a, b, c, d, e, f, g, h, i, j, k, l, m) (ra, rb, rc, rd, re, rf, rg, rh, ri, rj, rk, rl, rm) where
  sqlSelectCols esc (a, b, c, d, e, f, g, h, i, j, k, l, m) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      , sqlSelectCols esc h
      , sqlSelectCols esc i
      , sqlSelectCols esc j
      , sqlSelectCols esc k
      , sqlSelectCols esc l
      , sqlSelectCols esc m
      ]
  sqlSelectColCount   = sqlSelectColCount . from13P
  sqlSelectProcessRow = fmap to13 . sqlSelectProcessRow

from13P :: Proxy (a,b,c,d,e,f,g,h,i,j,k,l,m) -> Proxy ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),m)
from13P = const Proxy

to13 :: ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),m) -> (a,b,c,d,e,f,g,h,i,j,k,l,m)
to13 ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),m) = (a,b,c,d,e,f,g,h,i,j,k,l,m)

instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         , SqlSelect h rh
         , SqlSelect i ri
         , SqlSelect j rj
         , SqlSelect k rk
         , SqlSelect l rl
         , SqlSelect m rm
         , SqlSelect n rn
         ) => SqlSelect (a, b, c, d, e, f, g, h, i, j, k, l, m, n) (ra, rb, rc, rd, re, rf, rg, rh, ri, rj, rk, rl, rm, rn) where
  sqlSelectCols esc (a, b, c, d, e, f, g, h, i, j, k, l, m, n) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      , sqlSelectCols esc h
      , sqlSelectCols esc i
      , sqlSelectCols esc j
      , sqlSelectCols esc k
      , sqlSelectCols esc l
      , sqlSelectCols esc m
      , sqlSelectCols esc n
      ]
  sqlSelectColCount   = sqlSelectColCount . from14P
  sqlSelectProcessRow = fmap to14 . sqlSelectProcessRow

from14P :: Proxy (a,b,c,d,e,f,g,h,i,j,k,l,m,n) -> Proxy ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),(m,n))
from14P = const Proxy

to14 :: ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),(m,n)) -> (a,b,c,d,e,f,g,h,i,j,k,l,m,n)
to14 ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),(m,n)) = (a,b,c,d,e,f,g,h,i,j,k,l,m,n)

instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         , SqlSelect h rh
         , SqlSelect i ri
         , SqlSelect j rj
         , SqlSelect k rk
         , SqlSelect l rl
         , SqlSelect m rm
         , SqlSelect n rn
         , SqlSelect o ro
         ) => SqlSelect (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) (ra, rb, rc, rd, re, rf, rg, rh, ri, rj, rk, rl, rm, rn, ro) where
  sqlSelectCols esc (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      , sqlSelectCols esc h
      , sqlSelectCols esc i
      , sqlSelectCols esc j
      , sqlSelectCols esc k
      , sqlSelectCols esc l
      , sqlSelectCols esc m
      , sqlSelectCols esc n
      , sqlSelectCols esc o
      ]
  sqlSelectColCount   = sqlSelectColCount . from15P
  sqlSelectProcessRow = fmap to15 . sqlSelectProcessRow

from15P :: Proxy (a,b,c,d,e,f,g,h,i,j,k,l,m,n, o) -> Proxy ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),(m,n),o)
from15P = const Proxy

to15 :: ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),(m,n),o) -> (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)
to15 ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),(m,n),o) = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)

instance ( SqlSelect a ra
         , SqlSelect b rb
         , SqlSelect c rc
         , SqlSelect d rd
         , SqlSelect e re
         , SqlSelect f rf
         , SqlSelect g rg
         , SqlSelect h rh
         , SqlSelect i ri
         , SqlSelect j rj
         , SqlSelect k rk
         , SqlSelect l rl
         , SqlSelect m rm
         , SqlSelect n rn
         , SqlSelect o ro
         , SqlSelect p rp
         ) => SqlSelect (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p) (ra, rb, rc, rd, re, rf, rg, rh, ri, rj, rk, rl, rm, rn, ro, rp) where
  sqlSelectCols esc (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p) =
    uncommas'
      [ sqlSelectCols esc a
      , sqlSelectCols esc b
      , sqlSelectCols esc c
      , sqlSelectCols esc d
      , sqlSelectCols esc e
      , sqlSelectCols esc f
      , sqlSelectCols esc g
      , sqlSelectCols esc h
      , sqlSelectCols esc i
      , sqlSelectCols esc j
      , sqlSelectCols esc k
      , sqlSelectCols esc l
      , sqlSelectCols esc m
      , sqlSelectCols esc n
      , sqlSelectCols esc o
      , sqlSelectCols esc p
      ]
  sqlSelectColCount   = sqlSelectColCount . from16P
  sqlSelectProcessRow = fmap to16 . sqlSelectProcessRow

from16P :: Proxy (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p) -> Proxy ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),(m,n),(o,p))
from16P = const Proxy

to16 :: ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),(m,n),(o,p)) -> (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p)
to16 ((a,b),(c,d),(e,f),(g,h),(i,j),(k,l),(m,n),(o,p)) = (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p)


-- | Insert a 'PersistField' for every selected value.
--
-- /Since: 2.4.2/
insertSelect :: (MonadIO m, PersistEntity a) =>
  SqlQuery (SqlExpr (Insertion a)) -> SqlWriteT m ()
insertSelect = void . insertSelectCount

-- | Insert a 'PersistField' for every selected value, return the count afterward
insertSelectCount :: (MonadIO m, PersistEntity a) =>
  SqlQuery (SqlExpr (Insertion a)) -> SqlWriteT m Int64
insertSelectCount = rawEsqueleto INSERT_INTO . fmap EInsertFinal

-- | Renders an expression into 'Text'. Only useful for creating a textual
-- representation of the clauses passed to an "On" clause.
--
-- @since 3.2.0
renderExpr :: SqlBackend -> SqlExpr (Value Bool) -> T.Text
renderExpr sqlBackend e =
  case e of
    ERaw _ mkBuilderValues -> do
      let (builder, _) = mkBuilderValues (sqlBackend, initialIdentState)
       in (builderToText builder)
    ECompositeKey mkInfo ->
      throw
        . RenderExprUnexpectedECompositeKey
        . builderToText
        . mconcat
        . mkInfo
        $ (sqlBackend, initialIdentState)
    EAliasedValue i _   -> 
      builderToText $ useIdent (sqlBackend, initialIdentState) i
    EValueReference i i' -> 
      let (builder, _) = valueReferenceToRawSql i i' (sqlBackend, initialIdentState)
       in (builderToText builder)
-- | An exception thrown by 'RenderExpr' - it's not designed to handle composite
-- keys, and will blow up if you give it one.
--
-- @since 3.2.0
data RenderExprException = RenderExprUnexpectedECompositeKey T.Text
  deriving Show

-- |
--
-- @since 3.2.0
instance Exception RenderExprException
