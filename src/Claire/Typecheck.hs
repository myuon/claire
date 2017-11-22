{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
module Claire.Typecheck where

import Control.Monad.State
import Control.Monad.Catch
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Unique
import Data.Foldable

import Claire.Syntax
import Claire.Env

type UType = TypeForm Int

data InferError
  = UnificationFailed UType UType
  deriving (Show)

instance Exception InferError

unify :: MonadThrow m => UType -> UType -> m (UType -> UType)
unify x y | x == y = return $ id
unify (ConT con1 xs) (ConT con2 ys)
  | con1 == con2 && length xs == length ys = do
      let go (x,y) sbt = do {
            uf <- unify (sbt x) (sbt y);
            return $ uf . sbt
            }
      foldrM go id (zip xs ys)
  | otherwise = throwM $ UnificationFailed (ConT con1 xs) (ConT con2 ys)
unify (ArrT x1 x2) (ArrT y1 y2) = do
  unif2 <- unify x2 y2
  unif1 <- unify (unif2 x1) (unif2 y1)
  return $ unif1 . unif2
unify (VarT i) t
  | i `notElem` fvT t = return $ substType i t
  | VarT i == t = return $ id
  | otherwise = throwM $ UnificationFailed (VarT i) t
unify t (VarT i) = unify (VarT i) t
unify x y = throwM $ UnificationFailed x y  

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

inferT :: (MonadIO m, MonadThrow m) => M.Map Ident Type -> Term -> m UType
inferT env term = do
  typ0 <- VarT . hashUnique <$> liftIO newUnique

  let step typ (x,y) = do {
        uf <- unify x y;
        return $ uf typ
        }
  foldlM step typ0 =<< evalStateT (go term typ0) M.empty

  where
    go :: MonadIO m => Term -> UType -> StateT (M.Map Ident UType) m (S.Set (UType,UType))
    go (Var v) typ = do
      ctx <- get
      if M.member v ctx
        then return $ S.singleton (typ,ctx M.! v)
        else do
          modify $ M.insert v typ
          return S.empty
    go (Func v ts) typ | M.member v env = do
      vtyp <- utype $ env M.! v
      tyts <- replicateM (length ts) (VarT . hashUnique <$> liftIO newUnique)
      qs <- zipWithM go ts tyts
      return $ S.insert (foldr ArrT typ tyts,vtyp) $ S.unions qs


