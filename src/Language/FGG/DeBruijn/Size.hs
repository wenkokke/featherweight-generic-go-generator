{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
module Language.FGG.DeBruijn.Size where


import Language.FGG.Common
import Language.FGG.DeBruijn.Base


class Sized a where
  size :: a -> Int

instance Sized a => Sized (Vec a n) where
  size = vfoldr (\x y -> size x + y) 0

instance (Sized a, Sized b) => Sized (a, b) where
  size (x, y) = size x + size y

instance Sized (Type a ts ti) where
  size (Con _tc args) = 1 + size args
  size (Par _a) = 1

instance Sized (Prog ann) where
  size (FDecls _ann fds)
    = size fds

instance Sized (FDecls ann f) where
  size (NewF _ann fds)
    = 1 + size fds
  size (MDecls _ann mds)
    = size mds

instance Sized (MDecls ann f m) where
  size (NewM _ann mds)
    = 1 + size mds
  size (TyDecls _ann tys)
    = size tys

instance Sized (TyDecls ann ts ti f m) where
  size (LetStruct _ann parBnds fldTys tys)
    = 1 + size parBnds + size (vmap snd fldTys) + size tys
  size (LetInterface _ann parBnds parents msigs tys)
    = 1 + size parBnds + size parents + size (vmap snd msigs) + size tys
  size (TmDecls _ann tms)
    = size tms

instance Sized (TmDecls ann ts ti f m) where
  size (LetMethod _ann objParBnds _objTy _m methParBnds argTys retTy body tms)
    = 1 + size objParBnds + size methParBnds + size argTys + size retTy + size body + size tms
  size (Main _ann mainTy body)
    = size mainTy + size body

instance Sized (Expr ann a ts ti f m x) where
  size (Var _ann _x)
    = 1
  size (Struct _ann _ts tyArgs flds)
    = 1 + size tyArgs + size flds
  size (Select _ann obj objTy _f)
    = 1 + size obj + size objTy
  size (Call _ann obj objTy _m tyArgs args)
    = 1 + size obj + size objTy + size tyArgs + size args
  size (Assert _ann obj objTy assTy)
    = 1 + size obj + size objTy + size assTy

instance Sized (MSig a ts ti) where
  size (MSig parBnds _objTy argTys retTy)
    = size parBnds + size argTys + size retTy
