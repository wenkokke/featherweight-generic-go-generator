{-# LANGUAGE OverloadedStrings #-}

module Language.FGG.Named where

import Data.Text (Text)
import qualified Data.Text as T
import Data.List (intersperse)


-- * Named FG

type Name
  = Text

data Type
  = Par Name
  | Con Name [Type]
  deriving (Show)

data Expr
  = Var
    Name           -- ^ Variable name
  | Struct
    Name           -- ^ Struct name
    [Type]         -- ^ Type arguments
    [Expr]         -- ^ Field values
  | Select
    Expr           -- ^ Struct
    Name           -- ^ Field name
  | Call
    Expr           -- ^ Struct
    Name           -- ^ Method name
    [Type]         -- ^ Type arguments
    [Expr]         -- ^ Arguments
  | Assert
    Expr           -- ^ Struct
    Type           -- ^ Asserted type
  deriving (Show)

data Sig
  = Sig
    Name           -- ^ Method name
    [(Name, Type)] -- ^ Type parameters and bounds
    [(Name, Type)] -- ^ Method arguments and types
    Type           -- ^ Return type
  deriving (Show)

data Decl
  = LetStruct
    Name           -- ^ Struct name
    [(Name, Type)] -- ^ Type parameters and bounds
    [(Name, Type)] -- ^ Field names and types
  | LetInterface
    Name           -- ^ Interface name
    [(Name, Type)] -- ^ Type parameters and bounds
    [Type]         -- ^ Parent interfaces
    [Sig]          -- ^ Method signatures
  | LetMethod
    (Name, Name)   -- ^ Struct name
    [(Name, Type)] -- ^ Type parameters and bounds
    Sig            -- ^ Signature
    Expr           -- ^ Body
  deriving (Show)

data Prog
  = Prog [Decl] Expr
  deriving (Show)


-- * Pretty Printer

prettyParBnds :: [(Name, Type)] -> Text
prettyParBnds parBnds = "(type " <> parBnds' <> ")"
  where
    parBnds' =
      T.concat (intersperse ", " [ argName <> " " <> prettyType argBnd | (argName, argBnd) <- parBnds ])

prettyProg :: Prog -> Text
prettyProg (Prog ds e) = T.concat (intersperse ";\n" (["package main","import \"fmt\""] ++ ds' ++ [main]))
  where
    ds'  = prettyDecl <$> ds
    e'   = prettyExpr e
    main = "func main() {\n  fmt.Printf(\"%#v\", " <> e' <> ")\n}"

prettyDecl :: Decl -> Text
prettyDecl (LetStruct ts parBnds args) =
  "type " <> ts <> prettyParBnds parBnds <> " struct {\n" <> args' <> "\n}"
  where
    args' = T.concat . intersperse ";\n" $
      [ "  " <> argName <> " " <> prettyType argTy | (argName, argTy) <- args ]
prettyDecl (LetInterface ti parBnds parents sigs) =
  "type " <> ti <> prettyParBnds parBnds <> " interface {\n" <> parentsAndSigs' <> "\n}"
  where
    parentsAndSigs' = T.concat . intersperse ";\n" $
      [ "  " <> prettyType parent | parent <- parents ] ++
      [ "  " <> prettySig sig | sig <- sigs ]
prettyDecl (LetMethod (this, str) parBnds sig body) =
  "func (" <> this <> " " <> str <> prettyParBnds parBnds <> ") " <> sig' <> " {\n  return " <> body' <> "\n}"
  where
    sig' = prettySig sig
    body' = prettyExpr body

prettySig :: Sig -> Text
prettySig (Sig m parBnds args retTy) = m <> prettyParBnds parBnds <> "(" <> args' <> ")" <> " " <> retTy'
  where
    args' = T.concat (intersperse ", " [ argName <> " " <> prettyType argTy  | (argName, argTy) <- args ])
    retTy' = prettyType retTy

prettyExpr :: Expr -> Text
prettyExpr (Var x) = x
prettyExpr (Struct ts tyArgs flds) = ts' <> "{" <> flds' <> "}"
  where
    ts' = prettyType (Con ts tyArgs)
    flds' = T.concat (intersperse ", " (prettyExpr <$> flds))
prettyExpr (Select str fld) = str' <> "." <> fld
  where
    str' = prettyExpr str
prettyExpr (Call str m tyArgs args) = str' <> "." <> m <> "(" <> tyArgs' <> ")" <> "(" <> args' <> ")"
  where
    str' = prettyExpr str
    tyArgs' = T.concat (intersperse ", " (prettyType <$> tyArgs))
    args' = T.concat (intersperse ", " (prettyExpr <$> args))
prettyExpr (Assert str ty) = str' <> "." <> "(" <> ty' <> ")"
  where
    str' = prettyExpr str
    ty' = prettyType ty

prettyType :: Type -> Text
prettyType (Par a)      = a
prettyType (Con t args) = t <> "(" <> args' <> ")"
  where
    args' = T.concat (intersperse ", " (map prettyType args))
