{-# LANGUAGE ImplicitParams #-}

module Language.Granule.Checker.Errors where

import Language.Granule.Utils
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span

{- Helpers for error messages and checker control flow -}
data CheckerError
  = CheckerError (Maybe Span) String
  | GenericError (Maybe Span) String
  | GradingError (Maybe Span) String
  | KindError (Maybe Span) String
  | LinearityError (Maybe Span) String
  | PatternTypingError (Maybe Span) String
  | UnboundVariableError (Maybe Span) String
  | RefutablePatternError (Maybe Span) String
  | NameClashError (Maybe Span) String
  | DuplicatePatternError (Maybe Span) String
  deriving (Show, Eq)

instance UserMsg CheckerError where
  title CheckerError {} = "Checker error"
  title GenericError {} = "Type error"
  title GradingError {} = "Grading error"
  title KindError {} = "Kind error"
  title LinearityError {} = "Linearity error"
  title PatternTypingError {} = "Pattern typing error"
  title UnboundVariableError {} = "Unbound variable error"
  title RefutablePatternError {} = "Pattern is refutable"
  title NameClashError {} = "Name clash"
  title DuplicatePatternError {} = "Duplicate pattern"
  location (CheckerError sp _) = sp
  location (GenericError sp _) = sp
  location (GradingError sp _) = sp
  location (KindError sp _) = sp
  location (LinearityError sp _) = sp
  location (PatternTypingError sp _) = sp
  location (UnboundVariableError sp _) = sp
  location (RefutablePatternError sp _) = sp
  location (NameClashError sp _) = sp
  location (DuplicatePatternError sp _) = sp
  msg (CheckerError _ m) = m
  msg (GenericError _ m) = m
  msg (GradingError _ m) = m
  msg (KindError _ m) = m
  msg (LinearityError _ m) = m
  msg (PatternTypingError _ m) = m
  msg (UnboundVariableError _ m) = m
  msg (RefutablePatternError _ m) = m
  msg (NameClashError _ m) = m
  msg (DuplicatePatternError _ m) = m

data LinearityMismatch =
   LinearNotUsed Id
 | LinearUsedNonLinearly Id
 | NonLinearPattern
   deriving Show -- for debugging
