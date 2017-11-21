{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
module Claire.Typecheck where

import Control.Monad.State
import Control.Monad.Except
import Control.Unification
import Control.Unification.IntVar
import Control.Unification.Types
import qualified Data.Map as M

import Claire.Syntax
import Claire.Env

data UTypeForm t
  = UProp
  | UArrT t t
  | UConT Ident [t]
  deriving (Show, Functor, Foldable, Traversable)

type UType = UTerm UTypeForm IntVar

instance Unifiable UTypeForm where
  zipMatch = go where
    go :: UTypeForm t -> UTypeForm t -> Maybe (UTypeForm (Either t (t,t)))
    go UProp UProp = Just UProp
    go (UArrT tx ty) (UArrT sx sy) = return $ UArrT (Right (tx,sx)) (Right (ty,sy))
    go (UConT t ts) (UConT s ss) | t == s = return $ UConT t (zipWith (\x y -> Right (x,y)) ts ss)
    go _ _ = Nothing


inferTu :: (Monad m, MonadTrans em, MonadError (UFailure UTypeForm IntVar) (em (IntBindingT UTypeForm m)))
       => M.Map Ident UType -> Term -> em (IntBindingT UTypeForm m) UType
inferTu env term = go term . UVar =<< lift freeVar where
  go (Var v) typ | M.member v env = unify (env M.! v) typ
  go (Var v) typ = return typ
  go (Func v ts) typ = do
    tyts <- replicateM (length ts) $ fmap UVar $ lift freeVar
    go (Var v) $ foldr (\x y -> UTerm $ x `UArrT` y) typ tyts
    mapM_ (uncurry go) (zip ts tyts)
    applyBindings typ

inferu :: (Monad m, MonadTrans em, MonadError (UFailure UTypeForm IntVar) (em (IntBindingT UTypeForm m)))
      => Formula -> StateT (M.Map Ident UType) (em (IntBindingT UTypeForm m)) UType
inferu pred = go pred _Prop where
  _Prop = UTerm UProp
  
  go :: (Monad m, MonadTrans em, MonadError (UFailure UTypeForm IntVar) (em (IntBindingT UTypeForm m)))
      => Formula -> UType -> StateT (M.Map Ident UType) (em (IntBindingT UTypeForm m)) UType
  go (Pred p ts) typ = do
    env <- get
    tyts <- lift $ replicateM (length ts) $ fmap UVar $ lift freeVar
    lift $ unify (env M.! p) $ foldr (\x y -> UTerm $ x `UArrT` y) typ tyts
    forM_ (zip ts tyts) $ \(tm,ty) -> lift . unify ty =<< lift (inferTu env tm)
    lift $ applyBindings typ
  go Top typ = lift $ unify typ _Prop
  go Bottom typ = lift $ unify typ _Prop
  go (fml1 :/\: fml2) typ = go fml1 _Prop >> go fml2 _Prop >> lift (applyBindings typ)
  go (fml1 :\/: fml2) typ = go fml1 _Prop >> go fml2 _Prop >> lift (applyBindings typ)
  go (fml1 :==>: fml2) typ = go fml1 _Prop >> go fml2 _Prop >> lift (applyBindings typ)
  go (Forall v fml) typ = do
    vtyp <- fmap UVar $ lift $ lift $ freeVar
    modify $ M.insert v vtyp
    go fml _Prop
    lift $ applyBindings _Prop
  go (Exist v fml) typ = do
    vtyp <- fmap UVar $ lift $ lift $ freeVar
    modify $ M.insert v vtyp
    go fml _Prop
    lift $ applyBindings _Prop


