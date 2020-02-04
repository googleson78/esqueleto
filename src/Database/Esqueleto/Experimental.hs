{-# LANGUAGE AllowAmbiguousTypes
           , CPP
           , DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , FunctionalDependencies
           , GADTs
           , MultiParamTypeClasses
           , TypeFamilies
           , TypeOperators
           , UndecidableInstances
           , OverloadedStrings
 #-}

module Database.Esqueleto.Experimental where

import qualified Control.Monad.Trans.Writer as W
import qualified Control.Monad.Trans.State as S
import Control.Monad.Trans.Class (lift)
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif
import Data.Proxy (Proxy(..))
import Database.Esqueleto.Internal.PersistentImport
import Database.Esqueleto.Internal.Internal 
          ( SqlExpr(..)
          , InnerJoin(..)
          , CrossJoin(..)
          , LeftOuterJoin(..)
          , RightOuterJoin(..)
          , FullOuterJoin(..)
          , FromClause(..)
          , SqlQuery(..)
          , SideData(..)
          , Value(..)
          , JoinKind(..)
          , newIdentFor
          , SqlSelect(..)
          , Mode(..)
          , toRawSql
          , Ident(..)
          , to3, to4, to5, to6, to7, to8
          , from3, from4, from5, from6, from7, from8
          )

data (:&) a b = a :& b
infixl 2 :&

data SqlSetOperation a =
    Union (SqlSetOperation a) (SqlSetOperation a)
  | UnionAll (SqlSetOperation a) (SqlSetOperation a)
  | Except (SqlSetOperation a) (SqlSetOperation a)
  | Intersect (SqlSetOperation a) (SqlSetOperation a)
  | SelectQuery (SqlQuery a)

data From a where 
  Table         :: PersistEntity ent => From (SqlExpr (Entity ent))
  SubQuery      :: (SqlSelect (AliasType a) r, SqlSelect (ReferenceType (AliasType a)) r', ToAlias a , ToAliasReference (AliasType a))
                => SqlQuery a
                -> From (ReferenceType (AliasType a))
  SqlSetOperation :: (SqlSelect (AliasType a) r, ToAlias a, ToAliasReference (AliasType a)) 
                => SqlSetOperation a
                -> From (ReferenceType (AliasType a))
  InnerJoinFrom :: From a 
                -> (From b, (a :& b) -> SqlExpr (Value Bool)) 
                -> From (a :& b)
  CrossJoinFrom :: From a 
                -> From b 
                -> From (a :& b)
  LeftJoinFrom  :: ToMaybe b
                => From a 
                -> (From b, (a :& (MaybeType b)) -> SqlExpr (Value Bool))
                -> From (a :& (MaybeType b))
  RightJoinFrom :: ToMaybe a
                => From a 
                -> (From b, ((MaybeType a) :& b) -> SqlExpr (Value Bool)) 
                -> From ((MaybeType a) :& b)
  FullJoinFrom  :: (ToMaybe a, ToMaybe b)
                => From a 
                -> (From b, ((MaybeType a) :& (MaybeType b)) -> SqlExpr (Value Bool))
                -> From ((MaybeType a) :& (MaybeType b))

on :: ToFrom a => a -> b -> (a, b)
on = (,)
infix 9 `on`

{-- Type class magic to allow the use of the `InnerJoin` family of data constructors in from --}
class ToFrom a where
  type FromType a
  toFrom :: a -> From (FromType a)

instance ToFrom (From a) where
  type FromType (From a) = a
  toFrom = id

instance (SqlSelect (AliasType a) r, SqlSelect (ReferenceType (AliasType a)) r', ToAlias a, ToAliasReference (AliasType a)) => ToFrom (SqlSetOperation a) where
  type FromType (SqlSetOperation a) = ReferenceType (AliasType a)
  -- If someone uses just a plain SelectQuery it should behave like a normal subquery
  toFrom (SelectQuery q) = SubQuery q 
  -- Otherwise use the SqlSetOperation
  toFrom q = SqlSetOperation q

instance (ToFrom a, ToFrom b, ToMaybe (FromType b), a' ~ FromType a, mb ~ MaybeType (FromType b)) 
       => ToFrom (LeftOuterJoin a (b, (a' :& mb) -> SqlExpr (Value Bool))) where
  type FromType (LeftOuterJoin a (b, (a' :& mb) -> SqlExpr (Value Bool))) = ((FromType a) :& (MaybeType (FromType b)))
  toFrom (LeftOuterJoin lhs (rhs, on')) = LeftJoinFrom (toFrom lhs) (toFrom rhs, on')

instance (ToFrom a, ToFrom b, ToMaybe (FromType a), ToMaybe (FromType b), ma ~ (MaybeType (FromType a)), mb ~ (MaybeType (FromType b))) 
       => ToFrom (FullOuterJoin a (b, ((ma :& mb) -> SqlExpr (Value Bool)))) where
  type FromType (FullOuterJoin a (b, ((ma :& mb) -> SqlExpr (Value Bool)))) = ((MaybeType (FromType a)) :& (MaybeType (FromType b)))
  toFrom (FullOuterJoin lhs (rhs, on')) = FullJoinFrom (toFrom lhs) (toFrom rhs, on')

instance (ToFrom a, ToFrom b, ToMaybe (FromType a), ma ~ (MaybeType (FromType a)), b' ~ (FromType b)) 
       => ToFrom (RightOuterJoin a (b, (ma :& b') -> SqlExpr (Value Bool))) where
  type FromType (RightOuterJoin a (b, (ma :& b') -> SqlExpr (Value Bool))) = ((MaybeType (FromType a)) :& (FromType b))
  toFrom (RightOuterJoin lhs (rhs, on')) = RightJoinFrom (toFrom lhs) (toFrom rhs, on')

instance (ToFrom a, ToFrom b, a' ~ FromType a, b' ~ FromType b) => ToFrom (InnerJoin a (b, (a' :& b') -> SqlExpr (Value Bool))) where
  type FromType (InnerJoin a (b, (a' :& b') -> SqlExpr (Value Bool))) = ((FromType a) :& (FromType b))
  toFrom (InnerJoin lhs (rhs, on')) = InnerJoinFrom (toFrom lhs) (toFrom rhs, on')


instance (ToFrom a, ToFrom b) => ToFrom (CrossJoin a b) where
  type FromType (CrossJoin a b) = (FromType a :& FromType b)
  toFrom (CrossJoin lhs rhs) = CrossJoinFrom (toFrom lhs) (toFrom rhs)

class ToMaybe a where
  type MaybeType a 
  toMaybe :: a -> MaybeType a

instance ToMaybe (SqlExpr (Maybe a)) where
  type MaybeType (SqlExpr (Maybe a)) = (SqlExpr (Maybe a))
  toMaybe = id

instance ToMaybe (SqlExpr (Entity a)) where
  type MaybeType (SqlExpr (Entity a)) = (SqlExpr (Maybe (Entity a)))
  toMaybe = EMaybe

instance (ToMaybe a, ToMaybe b) => ToMaybe (a :& b) where
  type MaybeType (a :& b) = ((MaybeType a) :& (MaybeType b))
  toMaybe (a :& b) = (toMaybe a :& toMaybe b) 

instance (ToMaybe a, ToMaybe b) => ToMaybe (a,b) where
  type MaybeType (a, b) = ((MaybeType a), (MaybeType b))
  toMaybe (a, b) = (toMaybe a, toMaybe b)

instance ( ToMaybe a 
         , ToMaybe b 
         , ToMaybe c 
         ) => ToMaybe (a,b,c) where
  type MaybeType (a,b,c) = (MaybeType a,MaybeType b,MaybeType c)
  toMaybe = to3 . toMaybe . from3

instance ( ToMaybe a
         , ToMaybe b
         , ToMaybe c
         , ToMaybe d
         ) => ToMaybe (a,b,c,d) where
  type MaybeType (a,b,c,d) = (MaybeType a,MaybeType b,MaybeType c,MaybeType d)
  toMaybe = to4 . toMaybe . from4

instance ( ToMaybe a
         , ToMaybe b
         , ToMaybe c
         , ToMaybe d
         , ToMaybe e
         ) => ToMaybe (a,b,c,d,e) where
  type MaybeType (a,b,c,d,e) = (MaybeType a,MaybeType b,MaybeType c,MaybeType d,MaybeType e)
  toMaybe = to5 . toMaybe . from5

instance ( ToMaybe a
         , ToMaybe b
         , ToMaybe c
         , ToMaybe d
         , ToMaybe e
         , ToMaybe f
         ) => ToMaybe (a,b,c,d,e,f) where
  type MaybeType (a,b,c,d,e,f) = (MaybeType a,MaybeType b,MaybeType c,MaybeType d,MaybeType e,MaybeType f)
  toMaybe = to6 . toMaybe . from6

instance ( ToMaybe a
         , ToMaybe b
         , ToMaybe c
         , ToMaybe d
         , ToMaybe e
         , ToMaybe f
         , ToMaybe g
         ) => ToMaybe (a,b,c,d,e,f,g) where
  type MaybeType (a,b,c,d,e,f,g) = (MaybeType a,MaybeType b,MaybeType c,MaybeType d,MaybeType e,MaybeType f,MaybeType g)
  toMaybe = to7 . toMaybe . from7

instance ( ToMaybe a
         , ToMaybe b
         , ToMaybe c
         , ToMaybe d
         , ToMaybe e
         , ToMaybe f
         , ToMaybe g
         , ToMaybe h
         ) => ToMaybe (a,b,c,d,e,f,g,h) where
  type MaybeType (a,b,c,d,e,f,g,h) = (MaybeType a,MaybeType b,MaybeType c,MaybeType d,MaybeType e,MaybeType f,MaybeType g,MaybeType h)
  toMaybe = to8 . toMaybe . from8

from :: (ToFrom a, a' ~ FromType a) => a -> SqlQuery a'
from parts = do 
  (a, clause) <- runFrom $ toFrom parts
  Q $ W.tell mempty{sdFromClause=[clause]}
  pure a
    where
      runFrom :: From a -> SqlQuery (a, FromClause)
      runFrom e@Table = do 
        let ed = entityDef $ getVal e
        ident <- newIdentFor (entityDB ed)
        let entity = EEntity ident
        pure $ (entity, FromStart ident ed)
          where 
            getVal :: PersistEntity ent => From (SqlExpr (Entity ent)) -> Proxy ent
            getVal = const Proxy
      runFrom (SubQuery subquery) = do
          -- We want to update the IdentState without writing the query to side data
          (ret, sideData) <- Q $ W.censor (\_ -> mempty) $ W.listen $ unQ subquery
          aliasedValue <- toAlias ret
          -- Make a fake query with the aliased results, this allows us to ensure that the query is only run once
          let aliasedQuery = Q $ W.WriterT $ pure (aliasedValue, sideData)
          -- Add the FromQuery that renders the subquery to our side data
          subqueryAlias <- newIdentFor (DBName "q")
          -- Pass the aliased results of the subquery to the outer query
          -- create aliased references from the outer query results (e.g value from subquery will be `subquery`.`value`), 
          -- this is probably overkill as the aliases should already be unique but seems to be good practice.
          ref <- toAliasReference subqueryAlias aliasedValue 
          pure (ref , FromQuery subqueryAlias (\info -> toRawSql SELECT info aliasedQuery))

      runFrom (SqlSetOperation operation) = do
          (aliasedOperation, ret) <- aliasQueries operation
          ident <- newIdentFor (DBName "u")
          ref <- toAliasReference ident ret 
          pure (ref, FromQuery ident $ operationToSql aliasedOperation)

          where
            aliasQueries o =
              case o of
                SelectQuery q -> do 
                  (ret, sideData) <- Q $ W.censor (\_ -> mempty) $ W.listen $ unQ q
                  prevState <- Q $ lift S.get
                  aliasedRet <- toAlias ret
                  Q $ lift $ S.put prevState
                  pure (SelectQuery $ Q $ W.WriterT $ pure (aliasedRet, sideData), aliasedRet)
                Union     o1 o2 -> do
                  (o1', ret) <- aliasQueries o1
                  (o2', _  ) <- aliasQueries o2
                  pure (Union o1' o2', ret)
                UnionAll  o1 o2 -> do 
                  (o1', ret) <- aliasQueries o1
                  (o2', _  ) <- aliasQueries o2
                  pure (UnionAll o1' o2', ret)
                Except    o1 o2 -> do 
                  (o1', ret) <- aliasQueries o1
                  (o2', _  ) <- aliasQueries o2
                  pure (Except o1' o2', ret)
                Intersect o1 o2 -> do 
                  (o1', ret) <- aliasQueries o1
                  (o2', _  ) <- aliasQueries o2
                  pure (Intersect o1' o2', ret)

            operationToSql o info =
              case o of
                SelectQuery q   -> toRawSql SELECT info q
                Union     o1 o2 -> doSetOperation "UNION"     info o1 o2
                UnionAll  o1 o2 -> doSetOperation "UNION ALL" info o1 o2
                Except    o1 o2 -> doSetOperation "EXCEPT"    info o1 o2
                Intersect o1 o2 -> doSetOperation "INTERSECT" info o1 o2

            doSetOperation operationText info o1 o2 =
                  let 
                    (q1, v1) = operationToSql o1 info
                    (q2, v2) = operationToSql o2 info
                  in (q1 <> " " <> operationText <> " " <> q2, v1 <> v2)


      runFrom (InnerJoinFrom leftPart (rightPart, on')) = do 
        (leftVal, leftFrom) <- runFrom leftPart
        (rightVal, rightFrom) <- runFrom rightPart
        let ret = leftVal :& rightVal
        pure $ (ret, FromJoin leftFrom InnerJoinKind rightFrom (Just (on' ret)))
      runFrom (CrossJoinFrom leftPart rightPart) = do 
        (leftVal, leftFrom) <- runFrom leftPart
        (rightVal, rightFrom) <- runFrom rightPart
        let ret = leftVal :& rightVal
        pure $ (ret, FromJoin leftFrom CrossJoinKind rightFrom Nothing)
      runFrom (LeftJoinFrom leftPart (rightPart, on')) = do
        (leftVal, leftFrom) <- runFrom leftPart
        (rightVal, rightFrom) <- runFrom rightPart
        let ret = leftVal :& (toMaybe rightVal)
        pure $ (ret, FromJoin leftFrom LeftOuterJoinKind rightFrom (Just (on' ret)))
      runFrom (RightJoinFrom leftPart (rightPart, on')) = do 
        (leftVal, leftFrom) <- runFrom leftPart
        (rightVal, rightFrom) <- runFrom rightPart
        let ret = (toMaybe leftVal) :& rightVal
        pure $ (ret, FromJoin leftFrom RightOuterJoinKind rightFrom (Just (on' ret)))
      runFrom (FullJoinFrom leftPart (rightPart, on')) = do
        (leftVal, leftFrom) <- runFrom leftPart
        (rightVal, rightFrom) <- runFrom rightPart
        let ret = (toMaybe leftVal) :& (toMaybe rightVal)
        pure $ (ret, FromJoin leftFrom FullOuterJoinKind rightFrom (Just (on' ret)))

-- Tedious tuple magic
class ToAlias a where
  type AliasType a
  toAlias :: a -> SqlQuery (AliasType a)

instance ToAlias (SqlExpr (Value a)) where
  type AliasType (SqlExpr (Value a)) = SqlExpr (Value a)
  toAlias v@(EAliasedValue _ _) = pure v
  toAlias v = do 
    ident <- newIdentFor (DBName "v")
    pure $ EAliasedValue ident v

instance ToAlias (SqlExpr (Entity a)) where
  type AliasType (SqlExpr (Entity a)) = SqlExpr (Entity a)
  toAlias v@(EAliasedEntityReference _ _) = pure v
  toAlias v@(EAliasedEntity _ _) = pure v
  toAlias (EEntity tableIdent) = do 
    ident <- newIdentFor (DBName "v")
    pure $ EAliasedEntity ident tableIdent

instance ( ToAlias a, ToAlias b) => ToAlias (a,b) where
  type AliasType (a,b) = (AliasType a, AliasType b)
  toAlias (a,b) = (,) <$> toAlias a <*> toAlias b

instance ( ToAlias a 
         , ToAlias b 
         , ToAlias c 
         ) => ToAlias (a,b,c) where
  type AliasType (a,b,c) = (AliasType a, AliasType b, AliasType c)
  toAlias x = to3 <$> (toAlias $ from3 x)

instance ( ToAlias a
         , ToAlias b 
         , ToAlias c
         , ToAlias d 
         ) => ToAlias (a,b,c,d) where
  type AliasType (a,b,c,d) = (AliasType a, AliasType b, AliasType c, AliasType d)
  toAlias x = to4 <$> (toAlias $ from4 x)

instance ( ToAlias a 
         , ToAlias b 
         , ToAlias c 
         , ToAlias d 
         , ToAlias e 
         ) => ToAlias (a,b,c,d,e) where
  type AliasType (a,b,c,d,e) = (AliasType a, AliasType b, AliasType c, AliasType d, AliasType e)
  toAlias x = to5 <$> (toAlias $ from5 x)

instance ( ToAlias a
         , ToAlias b
         , ToAlias c
         , ToAlias d
         , ToAlias e
         , ToAlias f
         ) => ToAlias (a,b,c,d,e,f) where
  type AliasType (a,b,c,d,e,f) = (AliasType a, AliasType b, AliasType c, AliasType d, AliasType e, AliasType f)
  toAlias x = to6 <$> (toAlias $ from6 x)

instance ( ToAlias a
         , ToAlias b
         , ToAlias c
         , ToAlias d
         , ToAlias e
         , ToAlias f
         , ToAlias g
         ) => ToAlias (a,b,c,d,e,f,g) where
  type AliasType (a,b,c,d,e,f,g) = (AliasType a, AliasType b, AliasType c, AliasType d, AliasType e, AliasType f, AliasType g)
  toAlias x = to7 <$> (toAlias $ from7 x)

instance ( ToAlias a
         , ToAlias b
         , ToAlias c
         , ToAlias d
         , ToAlias e
         , ToAlias f
         , ToAlias g
         , ToAlias h
         ) => ToAlias (a,b,c,d,e,f,g,h) where
  type AliasType (a,b,c,d,e,f,g,h) = (AliasType a, AliasType b, AliasType c, AliasType d, AliasType e, AliasType f, AliasType g, AliasType h)
  toAlias x = to8 <$> (toAlias $ from8 x)


-- more tedious tuple magic 
class ToAliasReference a where
  type ReferenceType a
  toAliasReference :: Ident -> a -> SqlQuery (ReferenceType a) 

instance ToAliasReference (SqlExpr (Value a)) where
  type ReferenceType (SqlExpr (Value a)) = SqlExpr (Value a)
  toAliasReference aliasSource (EAliasedValue aliasIdent _) = pure $ EValueReference aliasSource (\_ -> aliasIdent)
  toAliasReference _           v@(ERaw _ _)                 = toAlias v
  toAliasReference _           v@(ECompositeKey _)          = toAlias v
  toAliasReference _           v@(EValueReference _ _)      = pure v 

instance ToAliasReference (SqlExpr (Entity a)) where
  type ReferenceType (SqlExpr (Entity a)) = SqlExpr (Entity a)
  toAliasReference aliasSource (EAliasedEntity ident _) = pure $ EAliasedEntityReference aliasSource ident
  toAliasReference _ e@(EEntity _) = toAlias e 
  toAliasReference _ e@(EAliasedEntityReference _ _) = pure e

instance ( ToAliasReference a, ToAliasReference b) => ToAliasReference (a, b) where
  type ReferenceType (a,b) = (ReferenceType a, ReferenceType b)
  toAliasReference ident (a,b) = (,) <$> (toAliasReference ident a) <*> (toAliasReference ident b)

instance ( ToAliasReference a 
         , ToAliasReference b 
         , ToAliasReference c 
         ) => ToAliasReference (a,b,c) where
  type ReferenceType (a,b,c) = (ReferenceType a, ReferenceType b, ReferenceType c)
  toAliasReference ident x = fmap to3 $ toAliasReference ident $ from3 x

instance ( ToAliasReference a 
         , ToAliasReference b 
         , ToAliasReference c 
         , ToAliasReference d 
         ) => ToAliasReference (a,b,c,d) where
  type ReferenceType (a,b,c,d) = (ReferenceType a, ReferenceType b, ReferenceType c, ReferenceType d)
  toAliasReference ident x = fmap to4 $ toAliasReference ident $ from4 x

instance ( ToAliasReference a
         , ToAliasReference b
         , ToAliasReference c
         , ToAliasReference d
         , ToAliasReference e
         ) => ToAliasReference (a,b,c,d,e) where
  type ReferenceType (a,b,c,d,e) = (ReferenceType a, ReferenceType b, ReferenceType c, ReferenceType d, ReferenceType e)
  toAliasReference ident x = fmap to5 $ toAliasReference ident $ from5 x

instance ( ToAliasReference a
         , ToAliasReference b
         , ToAliasReference c
         , ToAliasReference d
         , ToAliasReference e
         , ToAliasReference f
         ) => ToAliasReference (a,b,c,d,e,f) where
  type ReferenceType (a,b,c,d,e,f) = (ReferenceType a, ReferenceType b, ReferenceType c, ReferenceType d, ReferenceType e, ReferenceType f)
  toAliasReference ident x = to6 <$> (toAliasReference ident $ from6 x)

instance ( ToAliasReference a
         , ToAliasReference b
         , ToAliasReference c
         , ToAliasReference d
         , ToAliasReference e
         , ToAliasReference f
         , ToAliasReference g
         ) => ToAliasReference (a,b,c,d,e,f,g) where
  type ReferenceType (a,b,c,d,e,f,g) = (ReferenceType a, ReferenceType b, ReferenceType c, ReferenceType d, ReferenceType e, ReferenceType f, ReferenceType g)
  toAliasReference ident x = to7 <$> (toAliasReference ident $ from7 x)

instance ( ToAliasReference a
         , ToAliasReference b
         , ToAliasReference c
         , ToAliasReference d
         , ToAliasReference e
         , ToAliasReference f
         , ToAliasReference g
         , ToAliasReference h
         ) => ToAliasReference (a,b,c,d,e,f,g,h) where
  type ReferenceType (a,b,c,d,e,f,g,h) = (ReferenceType a, ReferenceType b, ReferenceType c, ReferenceType d, ReferenceType e, ReferenceType f, ReferenceType g, ReferenceType h)
  toAliasReference ident x = to8 <$> (toAliasReference ident $ from8 x)
