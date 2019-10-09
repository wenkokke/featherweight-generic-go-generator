{-# OPTIONS -fno-warn-partial-type-signatures #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE EmptyDataDeriving     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeApplications      #-}
module Language.FGG.DeBruijn.Base where



import Control.Enumerable
import Data.Bifunctor
import Language.FGG.Common



-- ** Programs

newtype Prog
  = FDecls (FDecls Z)
  deriving (Typeable)

instance Enumerable Prog where
  enumerate = share $ aconcat
    [ c1 FDecls
    ]


data FDecls f
  = NewF (FDecls (S f))
  | MDecls (MDecls f Z)
  deriving (Typeable)

instance ( Enumerable f
         ) => Enumerable (FDecls f) where
  enumerate = share $ aconcat
    [ pay . c1 $ NewF
    , c1 MDecls
    ]


data MDecls f m
  = NewM (MDecls f (S m))
  | TyDecls (TyDecls Z Z f m)
  deriving (Typeable)

instance ( Enumerable f
         , Enumerable m
         ) => Enumerable (MDecls f m) where
  enumerate = share $ aconcat
    [ pay . c1 $ NewM
    , c1 TyDecls
    ]



-- ** Type declarations

data TyDecls ts ti f m
  = forall a n.
    (Fin a) =>
    LetStruct
    (Vec (Type Z ts ti) a)        -- ^ The bounds of the parameters
    (Vec (f, Type a ts ti) n)     -- ^ Field types
    (TyDecls (S ts) ti f m)
  | forall a n p.
    (Fin a) =>
    LetInterface
    (Vec (Type Z ts ti) a)        -- ^ The bounds of the type parameters
    (Vec (Type a ts ti) p)        -- ^ Parent interfaces
    (Vec (m, MSig a ts (S ti)) n) -- ^ Method signatures
    (TyDecls ts (S ti) f m)
  | TmDecls (TmDecls ts ti f m)
  deriving (Typeable)

instance ( Enumerable ts
         , Enumerable ti
         , Enumerable f
         , Enumerable m
         ) => Enumerable (TyDecls ts ti f m) where
  enumerate = share $ aconcat
    [ -- * Structures
      pay . c3 $ LetStruct @ts @ti @f @m @Z         @Z
    , pay . c3 $ LetStruct @ts @ti @f @m @(S Z)     @Z
    , pay . c3 $ LetStruct @ts @ti @f @m @(S (S Z)) @Z
    , pay . c3 $ LetStruct @ts @ti @f @m @Z         @(S Z)
    , pay . c3 $ LetStruct @ts @ti @f @m @(S Z)     @(S Z)
    , pay . c3 $ LetStruct @ts @ti @f @m @(S (S Z)) @(S Z)
    , pay . c3 $ LetStruct @ts @ti @f @m @Z         @(S (S Z))
    , pay . c3 $ LetStruct @ts @ti @f @m @(S Z)     @(S (S Z))
    , pay . c3 $ LetStruct @ts @ti @f @m @(S (S Z)) @(S (S Z))
    , -- * Interfaces
      pay . c4 $ LetInterface @ts @ti @f @m @Z         @Z         @Z
    , pay . c4 $ LetInterface @ts @ti @f @m @(S Z)     @Z         @Z
    , pay . c4 $ LetInterface @ts @ti @f @m @(S (S Z)) @Z         @Z
    , pay . c4 $ LetInterface @ts @ti @f @m @Z         @(S Z)     @Z
    , pay . c4 $ LetInterface @ts @ti @f @m @(S Z)     @(S Z)     @Z
    , pay . c4 $ LetInterface @ts @ti @f @m @(S (S Z)) @(S Z)     @Z
    , pay . c4 $ LetInterface @ts @ti @f @m @Z         @(S (S Z)) @Z
    , pay . c4 $ LetInterface @ts @ti @f @m @(S Z)     @(S (S Z)) @Z
    , pay . c4 $ LetInterface @ts @ti @f @m @(S (S Z)) @(S (S Z)) @Z
    , pay . c4 $ LetInterface @ts @ti @f @m @Z         @Z         @(S Z)
    , pay . c4 $ LetInterface @ts @ti @f @m @(S Z)     @Z         @(S Z)
    , pay . c4 $ LetInterface @ts @ti @f @m @(S (S Z)) @Z         @(S Z)
    , pay . c4 $ LetInterface @ts @ti @f @m @Z         @(S Z)     @(S Z)
    , pay . c4 $ LetInterface @ts @ti @f @m @(S Z)     @(S Z)     @(S Z)
    , pay . c4 $ LetInterface @ts @ti @f @m @(S (S Z)) @(S Z)     @(S Z)
    , pay . c4 $ LetInterface @ts @ti @f @m @Z         @(S (S Z)) @(S Z)
    , pay . c4 $ LetInterface @ts @ti @f @m @(S Z)     @(S (S Z)) @(S Z)
    , pay . c4 $ LetInterface @ts @ti @f @m @(S (S Z)) @(S (S Z)) @(S Z)
    , pay . c4 $ LetInterface @ts @ti @f @m @Z         @Z         @(S (S Z))
    , pay . c4 $ LetInterface @ts @ti @f @m @(S Z)     @Z         @(S (S Z))
    , pay . c4 $ LetInterface @ts @ti @f @m @(S (S Z)) @Z         @(S (S Z))
    , pay . c4 $ LetInterface @ts @ti @f @m @Z         @(S Z)     @(S (S Z))
    , pay . c4 $ LetInterface @ts @ti @f @m @(S Z)     @(S Z)     @(S (S Z))
    , pay . c4 $ LetInterface @ts @ti @f @m @(S (S Z)) @(S Z)     @(S (S Z))
    , pay . c4 $ LetInterface @ts @ti @f @m @Z         @(S (S Z)) @(S (S Z))
    , pay . c4 $ LetInterface @ts @ti @f @m @(S Z)     @(S (S Z)) @(S (S Z))
    , pay . c4 $ LetInterface @ts @ti @f @m @(S (S Z)) @(S (S Z)) @(S (S Z))
    , c1 TmDecls
    ]



-- ** Term declarations

data TmDecls ts ti f m
  = forall a a' n.
    (Fin a', Fin a, Fin (a' :+ a)) =>
    LetMethod                            -- ^ Declaration of a method instance
    (Vec (Type Z ts ti) a)               -- ^ The bounds of the type parameters
    ts                                   -- ^ The struct name
    m                                    -- ^ The method which is declared
    (Vec (Type a ts ti) a')              -- ^ The bounds of the type parameters
    (Vec (Type (a' :+ a) ts ti) n)       -- ^ The types of the arguments
    (Type (a' :+ a) ts ti)               -- ^ The return type
    (Expr (a' :+ a) ts ti f m (S n))     -- ^ The method body
    (TmDecls ts ti f m)
  | Main                                 -- ^ The main function
    (Type Z ts ti)
    (Expr Z ts ti f m Z)
  deriving (Typeable)

instance ( Enumerable ts
         , Enumerable ti
         , Enumerable f
         , Enumerable m
         ) => Enumerable (TmDecls ts ti f m) where
  enumerate = share $ aconcat
    [ pay . c8 $ LetMethod @ts @ti @f @m @Z         @Z         @Z
    , pay . c8 $ LetMethod @ts @ti @f @m @(S Z)     @Z         @Z
    , pay . c8 $ LetMethod @ts @ti @f @m @(S (S Z)) @Z         @Z
    , pay . c8 $ LetMethod @ts @ti @f @m @Z         @(S Z)     @Z
    , pay . c8 $ LetMethod @ts @ti @f @m @(S Z)     @(S Z)     @Z
    , pay . c8 $ LetMethod @ts @ti @f @m @Z         @(S (S Z)) @Z
    , pay . c8 $ LetMethod @ts @ti @f @m @Z         @Z         @(S Z)
    , pay . c8 $ LetMethod @ts @ti @f @m @(S Z)     @Z         @(S Z)
    , pay . c8 $ LetMethod @ts @ti @f @m @(S (S Z)) @Z         @(S Z)
    , pay . c8 $ LetMethod @ts @ti @f @m @Z         @(S Z)     @(S Z)
    , pay . c8 $ LetMethod @ts @ti @f @m @(S Z)     @(S Z)     @(S Z)
    , pay . c8 $ LetMethod @ts @ti @f @m @Z         @(S (S Z)) @(S Z)
    , pay . c8 $ LetMethod @ts @ti @f @m @Z         @Z         @(S (S Z))
    , pay . c8 $ LetMethod @ts @ti @f @m @(S Z)     @Z         @(S (S Z))
    , pay . c8 $ LetMethod @ts @ti @f @m @(S (S Z)) @Z         @(S (S Z))
    , pay . c8 $ LetMethod @ts @ti @f @m @Z         @(S Z)     @(S (S Z))
    , pay . c8 $ LetMethod @ts @ti @f @m @(S Z)     @(S Z)     @(S (S Z))
    , pay . c8 $ LetMethod @ts @ti @f @m @Z         @(S (S Z)) @(S (S Z))
    , c2 Main
    ]



-- ** Expressions

data Expr a ts ti f m x
  = Var
    x                                           -- ^ Variable name
  | forall n1 n2.
    Struct
    ts                                          -- ^ Struct name
    (Vec (Type a ts ti) n1)                     -- ^ Type parameters
    (Vec (Expr a ts ti f m x, Type a ts ti) n2) -- ^ Struct arguments
  | Select
    (Expr a ts ti f m x)                        -- ^ Struct
    (Type a ts ti)                              -- ^ Struct type
    f                                           -- ^ Field name
  | forall n1 n2.
    Call
    (Expr a ts ti f m x)                        -- ^ Object
    (Type a ts ti)                              -- ^ Object type
    m                                           -- ^ Method name
    (Vec (Type a ts ti) n1)                     -- ^ Type parameters
    (Vec (Expr a ts ti f m x, Type a ts ti) n2) -- ^ Method arguments
  | Assert
    (Expr a ts ti f m x)                        -- ^ Expression
    (Type a ts ti)                              -- ^ Expression type
    (Type a ts ti)                              -- ^ Asserted type
  deriving (Typeable)

instance ( Enumerable a
         , Enumerable ts
         , Enumerable ti
         , Enumerable f
         , Enumerable m
         , Enumerable x
         ) => Enumerable (Expr a ts ti f m x) where
  enumerate = share $ aconcat
    [ pay . c1 $ Var
    , pay . c3 $ Struct @a @ts @ti @f @m @x @Z         @Z
    , pay . c3 $ Struct @a @ts @ti @f @m @x @(S Z)     @Z
    , pay . c3 $ Struct @a @ts @ti @f @m @x @(S (S Z)) @Z
    , pay . c3 $ Struct @a @ts @ti @f @m @x @Z         @(S Z)
    , pay . c3 $ Struct @a @ts @ti @f @m @x @(S Z)     @(S Z)
    , pay . c3 $ Struct @a @ts @ti @f @m @x @(S (S Z)) @(S Z)
    , pay . c3 $ Struct @a @ts @ti @f @m @x @Z         @(S (S Z))
    , pay . c3 $ Struct @a @ts @ti @f @m @x @(S Z)     @(S (S Z))
    , pay . c3 $ Struct @a @ts @ti @f @m @x @(S (S Z)) @(S (S Z))
    , pay . c3 $ Select
    , pay . c5 $ Call @a @ts @ti @f @m @x @Z         @Z
    , pay . c5 $ Call @a @ts @ti @f @m @x @(S Z)     @Z
    , pay . c5 $ Call @a @ts @ti @f @m @x @(S (S Z)) @Z
    , pay . c5 $ Call @a @ts @ti @f @m @x @Z         @(S Z)
    , pay . c5 $ Call @a @ts @ti @f @m @x @(S Z)     @(S Z)
    , pay . c5 $ Call @a @ts @ti @f @m @x @(S (S Z)) @(S Z)
    , pay . c5 $ Call @a @ts @ti @f @m @x @Z         @(S (S Z))
    , pay . c5 $ Call @a @ts @ti @f @m @x @(S Z)     @(S (S Z))
    , pay . c5 $ Call @a @ts @ti @f @m @x @(S (S Z)) @(S (S Z))
    , pay . c3 $ Assert
    ]



-- ** Types

data Type a ts ti
  = Par a
  | forall a'.
    (Fin a') =>
    Con (TyCon ts ti) (Vec (Type a ts ti) a')
  deriving (Typeable)

deriving instance (Show a, Show ts, Show ti) => Show (Type a ts ti)

instance ( Eq a
         , Eq ts
         , Eq ti
         ) => Eq (Type a ts ti) where
  Par a1  == Par a2  = a1 == a2
  Par _   == Con _ _ = False
  Con _ _ == Par _   = False
  Con tc1 args1 == Con tc2 args2
    | tc1 == tc2 =
      case vlength args1 `decEq` vlength args2 of
        Nothing   -> False
        Just Refl -> args1 == args2
    | otherwise  = False

instance ( Enumerable ts
         , Enumerable ti
         , Enumerable a
         ) => Enumerable (Type a ts ti) where
  enumerate = share $ aconcat
    [ pay . c2 $ Con @a @ts @ti @Z
    , pay . c2 $ Con @a @ts @ti @(S Z)
    , pay . c2 $ Con @a @ts @ti @(S (S Z))
    , pay . c1 $ Par
    ]

instance Bifunctor (Type a) where
  bimap _ _ (Par a) = Par a
  bimap f g (Con tc args) = Con (bimap f g tc) (vmap (bimap f g) args)

-- |Map over the parameter argument of types.
mapPar :: (a -> b) -> Type a ts ti -> Type b ts ti
mapPar f (Par a)       = Par (f a)
mapPar f (Con tc args) = Con tc (vmap (mapPar f) args)



-- ** Type signatures

data SSig a ts ti
  = forall n.
    SSig
    (Vec (Type a ts ti) n)
  deriving (Typeable)

instance Bifunctor (SSig a) where
  bimap f g (SSig argTys)
    = SSig (vmap (bimap f g) argTys)


data ISig a ts ti
  = ISig
  deriving (Typeable)

instance Bifunctor (ISig a) where
  bimap _ _ ISig
    = ISig


newtype FSig a ts ti
  = FSig
    (Type a ts ti)
  deriving (Typeable)

instance Bifunctor (FSig a) where
  bimap f g (FSig retTy)
    = FSig (bimap f g retTy)


data MSig a ts ti
  = forall a' n.
    (Fin a, Fin (a' :+ a)) =>
    MSig
    (Vec (Type a ts ti) a')        -- ^ Type parameter bounds
    (TyCon ts ti)                  -- ^ Object type
    (Vec (Type (a' :+ a) ts ti) n) -- ^ Arguments types
    (Type (a' :+ a) ts ti)         -- ^ Return type
  deriving (Typeable)

instance ( Fin a
         , Enumerable a
         , Enumerable ts
         , Enumerable ti
         ) => Enumerable (MSig a ts ti) where
  enumerate = share $ aconcat
    [ pay . c4 . plusFin @_ @a Z         $ MSig @a @ts @ti @Z         @Z
    , pay . c4 . plusFin @_ @a Z         $ MSig @a @ts @ti @(S Z)     @Z
    , pay . c4 . plusFin @_ @a Z         $ MSig @a @ts @ti @(S (S Z)) @Z
    , pay . c4 . plusFin @_ @a (S Z)     $ MSig @a @ts @ti @Z         @(S Z)
    , pay . c4 . plusFin @_ @a (S Z)     $ MSig @a @ts @ti @(S Z)     @(S Z)
    , pay . c4 . plusFin @_ @a (S Z)     $ MSig @a @ts @ti @(S (S Z)) @(S Z)
    , pay . c4 . plusFin @_ @a (S (S Z)) $ MSig @a @ts @ti @Z         @(S (S Z))
    , pay . c4 . plusFin @_ @a (S (S Z)) $ MSig @a @ts @ti @(S Z)     @(S (S Z))
    , pay . c4 . plusFin @_ @a (S (S Z)) $ MSig @a @ts @ti @(S (S Z)) @(S (S Z))
    ]

instance Bifunctor (MSig a) where
  bimap f g (MSig parBnds objTy argTys retTy)
    = MSig
      (vmap (bimap f g) parBnds)
      (bimap f g objTy)
      (vmap (bimap f g) argTys)
      (bimap f g retTy)


data TySig sig ts ti
  = forall a.
    (Fin a) =>
    TySig
    (Vec (Type Z ts ti) a)
    (sig a ts ti)

instance Bifunctor (TySig SSig) where
  bimap f g (TySig parBnds ssig)
    = TySig (vmap (bimap f g) parBnds) (bimap f g ssig)

instance Bifunctor (TySig ISig) where
  bimap f g (TySig parBnds isig)
    = TySig (vmap (bimap f g) parBnds) (bimap f g isig)

instance Bifunctor (TySig FSig) where
  bimap f g (TySig parBnds fsig)
    = TySig (vmap (bimap f g) parBnds) (bimap f g fsig)

instance Bifunctor (TySig MSig) where
  bimap f g (TySig parBnds msig)
    = TySig (vmap (bimap f g) parBnds) (bimap f g msig)


-- ** Substitution for type parameters


-- |Simultaneous substitutions for type parameters in types.
substType :: (a -> Type b ts ti) -> Type a ts ti -> Type b ts ti
substType s = go
  where
    go (Par a) = s a
    go (Con tc args) = Con tc (vmap go args)


-- |Simultaneous substitutions for type parameters in method signatures.
substMethSig :: forall a b ts ti.
                (Fin b)
             => (a -> Type b ts ti)
             -> MSig a ts ti
             -> MSig b ts ti
substMethSig s (MSig (parBnds :: Vec _ a') objTy (argTys :: Vec _ n) retTy)
  = plusFin @_ @b a' $ MSig parBnds' objTy argTys' retTy'
  where
    a' :: Nat a'
    a' = vlength parBnds

    parBnds' :: Vec (Type b ts ti) a'
    parBnds' = vmap (substType s) parBnds

    s' :: a' :+ a -> Type (a' :+ b) ts ti
    s' = raiseSubst a' s

    argTys' :: Vec (Type (a' :+ b) ts ti) n
    argTys' = vmap (substType s') argTys

    retTy' :: Type (a' :+ b) ts ti
    retTy' = substType s' retTy


-- |Raise substitutions.
raiseSubst :: forall a a' b ts ti.
              Nat a'
           -> (a -> Type b ts ti)
           -> ((a' :+ a) -> Type (a' :+ b) ts ti)
raiseSubst Z      s i      = s i
raiseSubst (S _ ) _ FZ     = Par FZ
raiseSubst (S a') s (FS i) = mapPar FS (raiseSubst a' s i)


-- |Simultaneous substitutions for type parameters in expressions.
substExpr :: (a -> Type b ts ti) -> Expr a ts ti f m x -> Expr b ts ti f m x
substExpr s = go1
  where
    go2
      = substType s
    go1 (Var x)
      = Var x
    go1 (Struct ts tyArgs args)
      = Struct ts (vmap go2 tyArgs) (vmap (bimap go1 go2) args)
    go1 (Select obj objTy f)
      = Select (go1 obj) (go2 objTy) f
    go1 (Call obj objTy m tyArgs args)
      = Call (go1 obj) (go2 objTy) m (vmap go2 tyArgs) (vmap (bimap go1 go2) args)
    go1 (Assert obj objTy assTy)
      = Assert (go1 obj) (go2 objTy) (go2 assTy)


-- * Extension to the combinators from Control.Enumerable

c8 :: ( Enumerable a
      , Enumerable b
      , Enumerable c
      , Enumerable d
      , Enumerable e
      , Enumerable g
      , Enumerable h
      , Enumerable i
      , Sized f
      , Typeable f
      ) => (a -> b -> c -> d -> e -> g -> h -> i -> x) -> Shareable f x
c8 f = c7 (uncurry f)

c9 :: ( Enumerable a
      , Enumerable b
      , Enumerable c
      , Enumerable d
      , Enumerable e
      , Enumerable g
      , Enumerable h
      , Enumerable i
      , Enumerable j
      , Sized f
      , Typeable f
      ) => (a -> b -> c -> d -> e -> g -> h -> i -> j -> x) -> Shareable f x
c9 f = c8 (uncurry f)

c10 :: ( Enumerable a
       , Enumerable b
       , Enumerable c
       , Enumerable d
       , Enumerable e
       , Enumerable g
       , Enumerable h
       , Enumerable i
       , Enumerable j
       , Enumerable k
       , Sized f
       , Typeable f
       ) => (a -> b -> c -> d -> e -> g -> h -> i -> j -> k -> x) -> Shareable f x
c10 f = c9 (uncurry f)

c11 :: ( Enumerable a
       , Enumerable b
       , Enumerable c
       , Enumerable d
       , Enumerable e
       , Enumerable g
       , Enumerable h
       , Enumerable i
       , Enumerable j
       , Enumerable k
       , Enumerable l
       , Sized f
       , Typeable f
       ) => (a -> b -> c -> d -> e -> g -> h -> i -> j -> k -> l -> x) -> Shareable f x
c11 f = c10 (uncurry f)

-- -}
-- -}
-- -}
-- -}
-- -}
