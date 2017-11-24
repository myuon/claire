{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
module Claire.Typecheck where

import Control.Monad.State.Strict
import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Unique
import Data.Foldable

import Claire.Syntax
import Claire.Env

type UType = TypeForm Int

data TypeError
  = UnificationFailed UType UType
  | NotFound Ident Env
  deriving (Show)

instance Exception TypeError

unify :: MonadThrow m => S.Set (UType,UType) -> m (UType -> UType)
unify eqs | S.null eqs = return id
unify eqs = do
  let ((x,y),qs) = S.deleteFindMin eqs
  f <- unify1 x y
  let qs' = S.map (\(x,y) -> (f x,f y)) qs
  fs <- unify qs'
  return $ f . fs

  where
  unify1 :: MonadThrow m => UType -> UType -> m (UType -> UType)
  unify1 x y | x == y = return $ id
  unify1 (ConT con1 xs) (ConT con2 ys)
    | con1 == con2 && length xs == length ys = do
        let go (x,y) sbt = do {
              uf <- unify1 (sbt x) (sbt y);
              return $ uf . sbt
              }
        foldrM go id (zip xs ys)
    | otherwise = throwM $ UnificationFailed (ConT con1 xs) (ConT con2 ys)
  unify1 (ArrT x1 x2) (ArrT y1 y2) = do
    unif2 <- unify1 x2 y2
    unif1 <- unify1 (unif2 x1) (unif2 y1)
    return $ unif1 . unif2
  unify1 (VarT i) t
    | i `notElem` fvT t = return $ substType i t
    | VarT i == t = return $ id
    | otherwise = throwM $ UnificationFailed (VarT i) t
  unify1 t (VarT i) = unify1 (VarT i) t
  unify1 x y = throwM $ UnificationFailed x y  

utype :: MonadIO m => Type -> m UType
utype t = evalStateT (go t) M.empty where
  go :: MonadIO m => Type -> StateT (M.Map Ident Int) m UType
  go (VarT i) = do
    ctx <- get
    if M.member i ctx
      then return $ VarT $ ctx M.! i
      else do
        n <- hashUnique <$> liftIO newUnique
        put (M.insert i n ctx)
        return (VarT n)
  go Prop = return Prop
  go (ArrT x y) = liftM2 ArrT (go x) (go y)
  go (ConT con xs) = liftM (ConT con) (mapM go xs)

inferT :: (MonadIO m, MonadThrow m) => Env -> Term -> StateT (M.Map Ident UType) m UType
inferT env term = do
  typ0 <- VarT . hashUnique <$> liftIO newUnique
  typecheckT env term typ0

typecheckT :: (MonadIO m, MonadThrow m) => Env -> Term -> UType -> StateT (M.Map Ident UType) m UType
typecheckT env term typ0 = do
  f <- unify =<< findUnifsT env term typ0
  return $ f typ0

findUnifsT :: MonadIO m => Env -> Term -> UType -> StateT (M.Map Ident UType) m (S.Set (UType,UType))
findUnifsT env = go
  where
    go :: MonadIO m => Term -> UType -> StateT (M.Map Ident UType) m (S.Set (UType,UType))
    go (Var v) typ | M.member v (types env) = do
      vtyp <- utype $ types env M.! v
      return $ S.singleton (typ,vtyp)
    go (Var v) typ = do
      ctx <- get
      if M.member v ctx
        then return $ S.singleton (typ,ctx M.! v)
        else do
          modify $ M.insert v typ
          return S.empty
    go (Abs xs t) typ = do
      tyt <- VarT . hashUnique <$> liftIO newUnique
      tyxs <- replicateM (length xs) (VarT . hashUnique <$> liftIO newUnique)
      zipWithM (\x xt -> modify $ M.insert x xt) xs tyxs
      qs <- go t tyt
      return $ S.insert (foldr ArrT typ tyxs,tyt) qs
    go (App t ts) typ = do
      tyts <- replicateM (length ts) (VarT . hashUnique <$> liftIO newUnique)
      q <- go t (foldr ArrT typ tyts)
      qs <- zipWithM go ts tyts
      return $ S.union q $ S.unions qs

inferST :: (MonadIO m, MonadThrow m) => Env -> Formula -> StateT (M.Map Ident UType) m UType
inferST env fml = do
  typ0 <- VarT . hashUnique <$> liftIO newUnique
  f <- unify =<< go fml typ0
  return $ f typ0

  where
    go :: (MonadIO m, MonadThrow m) => Formula -> UType -> StateT (M.Map Ident UType) m (S.Set (UType,UType))
    go (Pred p ts) typ | M.member p (types env) = do
      ptyp <- utype $ types env M.! p
      tyts <- replicateM (length ts) (VarT . hashUnique <$> liftIO newUnique)
      qs <- zipWithM (findUnifsT env) ts tyts
      return $ S.insert (typ,Prop) $ S.insert (foldr ArrT typ tyts,ptyp) $ S.unions qs
    go (Pred p ts) typ = do
      tyts <- replicateM (length ts) (VarT . hashUnique <$> liftIO newUnique)
      qs <- zipWithM (findUnifsT env) ts tyts
      modify $ M.insert p (foldr ArrT typ tyts)
      return $ S.insert (typ,Prop) $ S.unions qs
    go Top typ = return $ S.singleton (typ,Prop)
    go Bottom typ = return $ S.singleton (typ,Prop)
    go (fml1 :/\: fml2) typ = do
      eq1 <- go fml1 typ
      eq2 <- go fml2 typ
      return $ S.insert (typ,Prop) $ S.union eq1 eq2
    go (fml1 :\/: fml2) typ = do
      eq1 <- go fml1 typ
      eq2 <- go fml2 typ
      return $ S.insert (typ,Prop) $ S.union eq1 eq2
    go (fml1 :==>: fml2) typ = do
      eq1 <- go fml1 typ
      eq2 <- go fml2 typ
      return $ S.insert (typ,Prop) $ S.union eq1 eq2
    go (Forall t fml) typ = do
      eq <- go fml typ
      return $ S.insert (typ,Prop) eq
    go (Exist t fml) typ = do
      eq <- go fml typ
      return $ S.insert (typ,Prop) eq
    -- forall と exist については型も宣言できるようにしておいて
    -- その場合はcontextに追加する

infer :: (MonadIO m, MonadThrow m) => Env -> Formula -> m UType
infer env fml = evalStateT (inferST env fml) M.empty

