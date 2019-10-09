{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyDataDeriving   #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE RankNTypes          #-}

module Language.FGG.Common where


import Control.Enumerable
import Data.Bifunctor
import Data.Coolean
import Unsafe.Coerce


-- * Finite types

data Z
  deriving (Typeable, Eq, Ord, Show)

data S n
  = FZ
  | FS n
  deriving (Typeable, Eq, Ord, Show)

class (Ord n, Show n) => Fin n
instance Fin Z
instance Fin n => Fin (S n)

fromFS :: S n -> n
fromFS FZ = error "fromFS called on FZ"
fromFS (FS n) = n

instance Enumerable Z where
  enumerate = datatype []

instance Enumerable n => Enumerable (S n) where
  enumerate = share $ aconcat
    [ c0 FZ
    , c1 FS
    ]

type family m :+ n where
  Z   :+ n   = n
  S m :+ n   = S (m :+ n)

fromZ :: Z -> a
fromZ i = i `seq` error "instance of empty type Z"


-- * Natural number singletons

data Nat n where
  Z :: Nat Z
  S :: Nat n -> Nat (S n)
  deriving (Typeable)

toInt :: Nat n -> Int
toInt Z     = 0
toInt (S n) = 1 + toInt n

plus :: Nat n -> Nat m -> Nat (n :+ m)
Z     `plus` m = m
(S n) `plus` m = S (n `plus` m)

allFin :: Nat n -> Vec n n
allFin Z     = Nil
allFin (S n) = Cons FZ (vmap FS (allFin n))

inject :: Nat m -> n -> n :+ m
inject _ = unsafeCoerce

raise :: Nat n -> m -> n :+ m
raise Z     i = i
raise (S n) i = FS (raise n i)

lower :: Nat n -> n :+ m -> m
lower Z     i      = i
lower (S _) FZ     = error "lower n i called with n > i"
lower (S n) (FS i) = lower n i

hasEq :: Nat n -> forall a. (Eq n => a) -> a
hasEq = hasOrd

hasOrd :: Nat n -> forall a. (Ord n => a) -> a
hasOrd Z     x = x
hasOrd (S n) x = hasOrd n x

plusEq :: forall n m. Eq m => Nat n -> forall a. (Eq (n :+ m) => a) -> a
plusEq Z                  x = x
plusEq (S (n' :: Nat n')) x = plusEq @n' @m n' x

plusFin :: forall n m. Fin m => Nat n -> forall a. (Fin (n :+ m) => a) -> a
plusFin Z                  x = x
plusFin (S (n' :: Nat n')) x = plusFin @n' @m n' x


-- * Equality

data Id m n where
  Refl :: Id m m

congS :: Id m n -> Id (S m) (S n)
congS Refl = Refl

decEq :: Nat m -> Nat n -> Maybe (Id m n)
decEq Z     Z     = Just Refl
decEq (S m) (S n) = congS <$> decEq m n
decEq _     _     = Nothing


-- * Length-indexed vectors

data Vec a n where
  Nil :: Vec a Z
  Cons :: a -> Vec a n -> Vec a (S n)
  deriving (Typeable)

instance (Eq a) => Eq (Vec a n) where
  Nil       == Nil       = True
  Cons x xs == Cons y ys = x == y && xs == ys

deriving instance (Show a) => Show (Vec a n)

instance ( Typeable a
         ) => Enumerable (Vec a Z) where
  enumerate = share $ aconcat [ c0 Nil ]

instance ( Typeable n
         , Enumerable a
         , Enumerable (Vec a n)
         ) => Enumerable (Vec a (S n)) where
  enumerate = share $ aconcat [ c2 Cons ]

vmap :: (a -> b) -> Vec a n -> Vec b n
vmap _ Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

vlist :: Vec a n -> [a]
vlist Nil = []
vlist (Cons x xs) = x : vlist xs

vlength :: Vec a n -> Nat n
vlength Nil = Z
vlength (Cons _ xs) = S (vlength xs)

vlookup :: Vec a n -> n -> a
Nil       `vlookup` i      = fromZ i
Cons x _  `vlookup` FZ     = x
Cons _ xs `vlookup` (FS i) = xs `vlookup ` i

vlookupEither :: Vec a n -> Vec b m -> n :+ m -> Either a b
vlookupEither Nil         ys i      = Right (vlookup ys i)
vlookupEither (Cons x _)  _  FZ     = Left x
vlookupEither (Cons _ xs) ys (FS i) = vlookupEither xs ys i

vzip :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
vzip _ Nil Nil = Nil
vzip f (Cons x xs) (Cons y ys) = Cons (f x y) (vzip f xs ys)

vfoldr :: (a -> b -> b) -> b -> Vec a n -> b
vfoldr _ e Nil = e
vfoldr f e (Cons x xs) = f x (vfoldr f e xs)

vappend :: Vec a n1 -> Vec a n2 -> Vec a (n1 :+ n2)
Nil       `vappend` ys = ys
Cons x xs `vappend` ys = Cons x (xs `vappend` ys)

vall :: (a -> Bool) -> Vec a n -> Bool
vall p = vfoldr (\x b -> p x && b) True

vall' :: Coolean cool => (a -> cool) -> Vec a n -> Cool
vall' p = vfoldr (\x b -> p x &&& b) true

vand :: Vec Bool n -> Bool
vand = vfoldr (&&) True

vand' :: Coolean cool => Vec cool n -> Cool
vand' = vfoldr (&&&) true


-- * Type constructors

data TyCon ts ti
  = TyS ts
  | TyI ti
  deriving (Typeable, Eq, Show)

instance ( Enumerable ts
         , Enumerable ti
         ) => Enumerable (TyCon ts ti) where
  enumerate = share $ aconcat
    [ c1 TyS
    , c1 TyI
    ]

instance Bifunctor TyCon where
  bimap f _ (TyS ts) = TyS (f ts)
  bimap _ g (TyI ti) = TyI (g ti)
