{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}

module Syntax.Expr
  (AST(..), Value(..), Expr(..), Type(..), TypeScheme(..), Nat,
  letBox, valExpr,
  Def(..), DataDecl(..), Pattern(..), Coeffect(..),
  NatModifier(..), Effect, Kind(..), DataConstr(..), Cardinality,
  Id(..), mkId,
  Operator,
  arity, freeVars, subst, freshen, Freshener, freshenAST,
  normalise,
  nullSpan, getSpan, getEnd, getStart, Pos, Span,
  typeFoldM, TypeFold(..), resultType,
  mFunTy, mTyCon, mBox, mDiamond, mTyVar, mTyApp,
  mTyInt, mTyInfix,
  baseTypeFold,
  con, var, (.->), (.@)
  ) where

import Data.List ((\\), delete)
import Control.Monad.Trans.State.Strict
import Control.Monad (forM)
import Control.Arrow
import GHC.Generics (Generic)
import Data.Functor.Identity (runIdentity)
import Data.Text (Text)

import qualified System.IO as SIO (Handle)
import qualified Control.Concurrent.Chan as CC

import Context
import Syntax.FirstParameter
import Syntax.Identifiers
import Syntax.Span

-- | Natural numbers
type Nat = Word

-- Constructors and operators are just strings
type Operator = String

-- Values in Granule
data Value = Abs Pattern (Maybe Type) Expr
           | NumInt Int
           | NumFloat Double
           | Promote Expr
           | Pure Expr
           | Var Id
           | Constr Id [Value]
           | CharLiteral Char
           | StringLiteral Text
           -------------------------
           -- Used only inside the interpeter
           --
           -- Primitive functions (builtins)
           | Primitive (Value -> IO Value)

           -- Primitive operations that also close over the context
           | PrimitiveClosure (Ctxt Value -> Value -> IO Value)

           -- File handler
           | Handle SIO.Handle

           -- Channels
           | Chan (CC.Chan Value)

valExpr :: Value -> Expr
valExpr = Val nullSpan

deriving instance Show Value

instance Show (CC.Chan Value) where
  show _ = "Some channel"

instance Show (Value -> IO Value) where
  show _ = "Some primitive"

instance Show (Ctxt Value -> Value -> IO Value) where
  show _ = "Some primitive closure"

-- Expressions (computations) in Granule
data Expr = App Span Expr Expr
          | Binop Span Operator Expr Expr
          | LetDiamond Span Pattern (Maybe Type) Expr Expr
          | Val Span Value
          | Case Span Expr [(Pattern, Expr)]
          deriving (Generic)

deriving instance Show Expr

instance FirstParameter Expr Span

-- Syntactic sugar constructor
letBox :: Span -> Pattern -> Expr -> Expr -> Expr
letBox s pat e1 e2 =
  App s (Val s (Abs (PBox s pat) Nothing e2)) e1

-- Pattern matches
data Pattern
  = PVar Span Id               -- Variable patterns
  | PWild Span                 -- Wildcard (underscore) pattern
  | PBox Span Pattern          -- Box patterns
  | PInt Span Int              -- Numeric patterns
  | PFloat Span Double         -- Float pattern
  | PConstr Span Id [Pattern]  -- Constructor pattern
  deriving (Eq, Show, Generic)

instance FirstParameter Pattern Span

boundVars :: Pattern -> [Id]
boundVars (PVar _ v)     = [v]
boundVars PWild {}       = []
boundVars (PBox _ p)     = boundVars p
boundVars PInt {}        = []
boundVars PFloat {}      = []
boundVars (PConstr _ _ ps) = concatMap boundVars ps

instance Freshenable Pattern where
  freshen :: Pattern -> Freshener Pattern
  freshen (PVar s var) = do
      var' <- freshVar Value var
      return $ PVar s var'
  freshen (PBox s p) = do
      p' <- freshen p
      return $ PBox s p'
  freshen (PConstr s name ps) = do
      ps <- mapM freshen ps
      return (PConstr s name ps)
  freshen p@PWild {} = return p
  freshen p@PInt {} = return p
  freshen p@PFloat {} = return p

-- | The freshening monad for alpha-conversion to avoid name capturing
type Freshener t = State FreshenerState t

data FreshenerState = FreshenerState
  { counter :: Nat -- ^ fresh Id counter
  , varMap :: [(String, String)] -- ^ mapping of variables to their freshened names
  , tyMap :: [(String, String)] -- ^ mapping of type variables to their freshened names
  } deriving Show

-- | Given something freshenable, e.g. the AST, run the freshener on it and return the final state
-- >>> runFreshener (PVar ((0,0),(0,0)) (Id "x" "x"))
-- PVar ((0,0),(0,0)) (Id "x" "x_0")
runFreshener :: Freshenable t => t -> t
runFreshener x = evalState (freshen x) FreshenerState { counter = 0, varMap = [], tyMap = [] }

class Term t where
  -- Compute the free variables in an open term
  freeVars :: t -> [Id]

class Substitutable t where
  -- Syntactic substitution of a term into an expression
  -- (assuming variables are all unique to avoid capture)
  subst :: Expr -> Id -> t -> Expr

class Freshenable t where
  -- Alpha-convert bound variables to avoid name capturing
  freshen :: t -> Freshener t

-- Used to distinguish the value-level and type-level variables
data IdSyntacticCategory = Value | Type

-- Helper in the Freshener monad, creates a fresh id (and
-- remembers the mapping).
freshVar :: IdSyntacticCategory -> Id -> Freshener Id
freshVar cat var = do
    st <- get
    let var' = sourceName var ++ "_" ++ show (counter st)
    case cat of
      Value -> put st { counter = (counter st) + 1, varMap = (sourceName var, var') : (varMap st) }
      Type  -> put st { counter = (counter st) + 1,  tyMap = (sourceName var, var') :  (tyMap st) }
    return var { internalName = var' }

-- | Look up a variable in the freshener state.
-- If @Nothing@ then the variable name shouldn't change
lookupVar :: IdSyntacticCategory -> Id -> Freshener (Maybe String)
lookupVar cat v = do
  st <- get
  case cat of
    Value -> return . lookup (sourceName v) . varMap $ st
    Type  -> return . lookup (sourceName v) .  tyMap $ st

removeFreshenings :: [Id] -> Freshener ()
removeFreshenings [] = return ()
removeFreshenings (x:xs) = do
    st <- get
    put st { varMap = delete x' (varMap st) }
    removeFreshenings xs
  where
    x' = (sourceName x, internalName x)

instance Term Type where
  freeVars = runIdentity . typeFoldM TypeFold
    { tfFunTy   = \x y -> return $ x ++ y
    , tfTyCon   = \_ -> return [] -- or: const (return [])
    , tfBox     = \c t -> return $ freeVars c ++ t
    , tfDiamond = \_ x -> return x
    , tfTyVar   = \v -> return [v] -- or: return . return
    , tfTyApp   = \x y -> return $ x ++ y
    , tfTyInt   = \_ -> return []
    , tfTyInfix = \_ y z -> return $ y ++ z
    }

instance Freshenable Type where
  freshen =
    typeFoldM (baseTypeFold { tfTyApp = rewriteTyApp,
                              tfTyVar = freshenTyVar,
                              tfBox = freshenTyBox })
    where
      -- Rewrite type aliases of Box
      rewriteTyApp t1@(TyCon ident) t2
        | internalName ident == "Box" || internalName ident == "◻" =
          return $ Box (CInfinity (TyCon $ mkId "Cartesian")) t2
      rewriteTyApp t1 t2 = return $ TyApp t1 t2

      freshenTyBox c t = do
        c' <- freshen c
        t' <- freshen t
        return $ Box c' t'
      freshenTyVar v = do
        v' <- lookupVar Type v
        case v' of
           Just v' -> return (TyVar $ Id (sourceName v) v')
           -- This case happens if we are referring to a defined
           -- function which does not get its name freshened
           Nothing -> return (TyVar $ mkId (sourceName v))

instance Term Coeffect where
    freeVars (CVar v) = [v]
    freeVars (CPlus c1 c2) = freeVars c1 ++ freeVars c2
    freeVars (CTimes c1 c2) = freeVars c1 ++ freeVars c2
    freeVars (CExpon c1 c2) = freeVars c1 ++ freeVars c2
    freeVars (CMeet c1 c2) = freeVars c1 ++ freeVars c2
    freeVars (CJoin c1 c2) = freeVars c1 ++ freeVars c2
    freeVars CNat{}  = []
    freeVars CNatOmega{} = []
    freeVars CFloat{} = []
    freeVars CInfinity{} = []
    freeVars CZero{} = []
    freeVars COne{} = []
    freeVars Level{} = []
    freeVars CSet{} = []
    freeVars (CSig c _) = freeVars c

instance Freshenable Coeffect where
    freshen (CVar v) = do
      v' <- lookupVar Type v
      case v' of
        Just v' -> return $ CVar $ Id (sourceName v) v'
        Nothing -> return $ CVar $ mkId (sourceName v)

    freshen (CInfinity (TyVar i@(Id _ ""))) = do
      t <- freshVar Type i
      return $ CInfinity (TyVar t)

    freshen (CInfinity (TyVar i@(Id _ " infinity"))) = do
      t <- freshVar Type i
      return $ CInfinity (TyVar t)

    freshen (CPlus c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CPlus c1' c2'

    freshen (CTimes c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CTimes c1' c2'

    freshen (CExpon c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CExpon c1' c2'

    freshen (CMeet c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CMeet c1' c2'
    freshen (CJoin c1 c2) = do
      c1' <- freshen c1
      c2' <- freshen c2
      return $ CJoin c1' c2'

    freshen (CSet cs) = do
       cs' <- mapM (\(s, t) -> freshen t >>= (\t' -> return (s, t'))) cs
       return $ CSet cs'
    freshen (CSig c k) = do
      c' <- freshen c
      return $ CSig c' k
    freshen c@CInfinity{} = return c
    freshen c@CFloat{} = return c
    freshen c@CZero{}  = return c
    freshen c@COne{}   = return c
    freshen c@Level{}  = return c
    freshen c@CNat{}   = return c
    freshen c@CNatOmega{} = return c


instance Term Value where
    freeVars (Abs p _ e) = freeVars e \\ boundVars p
    freeVars (Var x)     = [x]
    freeVars (Pure e)    = freeVars e
    freeVars (Promote e) = freeVars e
    freeVars (NumInt _) = []
    freeVars (NumFloat _) = []
    freeVars (Constr _ _) = []
    freeVars (CharLiteral _) = []
    freeVars (StringLiteral _) = []
    freeVars (Handle{}) = []
    freeVars (Chan{})   = []

instance Substitutable Value where
    subst es v (Abs w t e)      = Val nullSpan $ Abs w t (subst es v e)
    subst es v (Pure e)         = Val nullSpan $ Pure (subst es v e)
    subst es v (Promote e)      = Val nullSpan $ Promote (subst es v e)
    subst es v (Var w) | v == w = es
    subst _ _ v@(NumInt _)        = Val nullSpan v
    subst _ _ v@(NumFloat _)      = Val nullSpan v
    subst _ _ v@(Var _)           = Val nullSpan v
    subst _ _ v@(Constr _ _)      = Val nullSpan v
    subst _ _ v@CharLiteral{}     = Val nullSpan v
    subst _ _ v@StringLiteral{}   = Val nullSpan v
    subst _ _ v@Handle{}          = Val nullSpan v
    subst _ _ v@Chan{}            = Val nullSpan v
    subst _ _ v@Primitive{}       = Val nullSpan v
    subst _ _ v@PrimitiveClosure{} = Val nullSpan v

instance Freshenable Value where
    freshen (Abs p t e) = do
      p'   <- freshen p
      e'   <- freshen e
      t'   <- case t of
                Nothing -> return Nothing
                Just ty -> freshen ty >>= (return . Just)
      removeFreshenings (boundVars p')
      return $ Abs p' t' e'

    freshen (Pure e) = do
      e' <- freshen e
      return $ Pure e'

    freshen (Promote e) = do
      e' <- freshen e
      return $ Promote e'

    freshen (Var v) = do
      v' <- lookupVar Value v
      case v' of
         Just v' -> return (Var $ Id (sourceName v) v')
         -- This case happens if we are referring to a defined
         -- function which does not get its name freshened
         Nothing -> return (Var $ Id (sourceName v) (sourceName v))

    freshen v@(NumInt _)   = return v
    freshen v@(NumFloat _) = return v
    freshen v@(Constr _ _) = return v
    freshen v@CharLiteral{} = return v
    freshen v@StringLiteral{} = return v

instance Term Expr where
    freeVars (App _ e1 e2)            = freeVars e1 ++ freeVars e2
    freeVars (Binop _ _ e1 e2)        = freeVars e1 ++ freeVars e2
    freeVars (LetDiamond _ p _ e1 e2) = freeVars e1 ++ (freeVars e2 \\ boundVars p)
    freeVars (Val _ e)                = freeVars e
    freeVars (Case _ e cases)         = freeVars e ++ (concatMap (freeVars . snd) cases
                                      \\ concatMap (boundVars . fst) cases)

instance Substitutable Expr where
    subst es v (App s e1 e2)        = App s (subst es v e1) (subst es v e2)
    subst es v (Binop s op e1 e2)   = Binop s op (subst es v e1) (subst es v e2)
    subst es v (LetDiamond s w t e1 e2) =
                                   LetDiamond s w t (subst es v e1) (subst es v e2)
    subst es v (Val _ val)          = subst es v val
    subst es v (Case s expr cases)  = Case s
                                     (subst es v expr)
                                     (map (second (subst es v)) cases)

instance Freshenable Expr where
    freshen (App s e1 e2) = do
      e1 <- freshen e1
      e2 <- freshen e2
      return $ App s e1 e2

    freshen (LetDiamond s p t e1 e2) = do
      e1 <- freshen e1
      p  <- freshen p
      e2 <- freshen e2
      t   <- case t of
                Nothing -> return Nothing
                Just ty -> freshen ty >>= (return . Just)
      return $ LetDiamond s p t e1 e2

    freshen (Binop s op e1 e2) = do
      e1 <- freshen e1
      e2 <- freshen e2
      return $ Binop s op e1 e2

    freshen (Case s expr cases) = do
      expr     <- freshen expr
      cases <- forM cases $ \(p, e) -> do
                  p <- freshen p
                  e <- freshen e
                  removeFreshenings (boundVars p)
                  return (p, e)
      return (Case s expr cases)

    freshen (Val s v) = do
     v <- freshen v
     return (Val s v)

--------- Definitions

data AST = AST [DataDecl] [Def] deriving Show

data Def = Def Span Id Expr [Pattern] TypeScheme
  deriving (Generic, Show)

instance FirstParameter Def Span

data DataDecl = DataDecl Span Id [(Id,Kind)] (Maybe Kind) [DataConstr]
  deriving (Generic, Show)

instance FirstParameter DataDecl Span

data DataConstr
  = DataConstrG Span Id TypeScheme
  | DataConstrA Span Id [Type]
  deriving (Eq, Show, Generic)

instance FirstParameter DataConstr Span

-- | How many data constructors a type has (Nothing -> don't know)
type Cardinality = Maybe Nat

freshenAST :: AST -> AST
freshenAST (AST dds defs) = AST dds (map runFreshener defs)

{-| Alpha-convert all bound variables of a definition, modulo the things on the lhs
Eg this:
@
foo : Int -> Int
foo x = (\(x : Int) -> x * 2) x
@
will become
@
foo : Int -> Int
foo x = (\(x0 : Int) -> x0 * 2) x
@

>>> runFreshener $ Def ((1,1),(2,29)) (Id "foo" "foo") (App ((2,10),(2,29)) (Val ((2,10),(2,25)) (Abs (PVar ((2,12),(2,12)) (Id "x" "x0")) (Just (TyCon (Id "Int" "Int"))) (Binop ((2,25),(2,25)) "*" (Val ((2,24),(2,24)) (Var (Id "x" "x0"))) (Val ((2,26),(2,26)) (NumInt 2))))) (Val ((2,29),(2,29)) (Var (Id "x" "x")))) [PVar ((2,5),(2,5)) (Id "x" "x")] (Forall ((0,0),(0,0)) [] (FunTy (TyCon (Id "Int" "Int")) (TyCon (Id "Int" "Int"))))
Def ((1,1),(2,29)) (Id "foo" "foo") (App ((2,10),(2,29)) (Val ((2,10),(2,25)) (Abs (PVar ((2,12),(2,12)) (Id "x" "x_1")) (Just (TyCon (Id "Int" "Int"))) (Binop ((2,25),(2,25)) "*" (Val ((2,24),(2,24)) (Var (Id "x" "x_1"))) (Val ((2,26),(2,26)) (NumInt 2))))) (Val ((2,29),(2,29)) (Var (Id "x" "x_0")))) [PVar ((2,5),(2,5)) (Id "x" "x_0")] (Forall ((0,0),(0,0)) [] (FunTy (TyCon (Id "Int" "Int")) (TyCon (Id "Int" "Int"))))
-}
instance Freshenable Def where
  freshen (Def s var e ps t) = do
    ps <- mapM freshen ps
    t  <- freshen t
    e  <- freshen e
    return (Def s var e ps t)

instance Term Def where
  freeVars (Def _ name body binders _) = delete name (freeVars body \\ concatMap boundVars binders)

----------- Types

data TypeScheme = Forall Span [(Id, Kind)] Type -- [(Id, Kind)] are the binders
    deriving (Eq, Show, Generic)

instance FirstParameter TypeScheme Span

instance Freshenable TypeScheme where
  freshen :: TypeScheme -> Freshener TypeScheme
  freshen (Forall s binds ty) = do
        binds' <- mapM (\(v, k) -> do { v' <- freshVar Type v; return (v', k) }) binds
        ty' <- freshen ty
        return $ Forall s binds' ty'

{-| Types.
Example: `List n Int` is `TyApp (TyApp (TyCon "List") (TyVar "n")) (TyCon "Int") :: Type`
-}
data Type = FunTy Type Type           -- ^ Function type
          | TyCon Id                  -- ^ Type constructor
          | Box Coeffect Type         -- ^ Coeffect type
          | Diamond Effect Type       -- ^ Effect type
          | TyVar Id                  -- ^ Type variable
          | TyApp Type Type           -- ^ Type application
          | TyInt Int                 -- ^ Type-level Int
          | TyInfix Operator Type Type  -- ^ Infix type operator
    deriving (Eq, Ord, Show)

-- Smart constructors for types
con :: String -> Type
con = TyCon . mkId

var :: String -> Type
var = TyVar . mkId

(.->) :: Type -> Type -> Type
s .-> t = FunTy s t

(.@) :: Type -> Type -> Type
s .@ t = TyApp s t

-- Trivially effectful monadic constructors
mFunTy :: Monad m => Type -> Type -> m Type
mFunTy x y   = return (FunTy x y)
mTyCon :: Monad m => Id -> m Type
mTyCon       = return . TyCon
mBox :: Monad m => Coeffect -> Type -> m Type
mBox c y     = return (Box c y)
mDiamond :: Monad m => Effect -> Type -> m Type
mDiamond e y = return (Diamond e y)
mTyVar :: Monad m => Id -> m Type
mTyVar       = return . TyVar
mTyApp :: Monad m => Type -> Type -> m Type
mTyApp x y   = return (TyApp x y)
mTyInt :: Monad m => Int -> m Type
mTyInt       = return . TyInt
mTyInfix :: Monad m => Operator -> Type -> Type -> m Type
mTyInfix op x y  = return (TyInfix op x y)

baseTypeFold :: Monad m => TypeFold m Type
baseTypeFold =
  TypeFold mFunTy mTyCon mBox mDiamond mTyVar mTyApp mTyInt mTyInfix

data TypeFold m a = TypeFold
  { tfFunTy   :: a -> a        -> m a
  , tfTyCon   :: Id -> m a
  , tfBox     :: Coeffect -> a -> m a
  , tfDiamond :: Effect -> a   -> m a
  , tfTyVar   :: Id            -> m a
  , tfTyApp   :: a -> a        -> m a
  , tfTyInt   :: Int           -> m a
  , tfTyInfix :: Operator -> a -> a -> m a }

-- | Monadic fold on a `Type` value
typeFoldM :: Monad m => TypeFold m a -> Type -> m a
typeFoldM algebra = go
  where
   go (FunTy t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfFunTy algebra) t1' t2'
   go (TyCon s) = (tfTyCon algebra) s
   go (Box c t) = do
     t' <- go t
     (tfBox algebra) c t'
   go (Diamond c t) = do
     t' <- go t
     (tfDiamond algebra) c t'
   go (TyVar v) = (tfTyVar algebra) v
   go (TyApp t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyApp algebra) t1' t2'
   go (TyInt i) = (tfTyInt algebra) i
   go (TyInfix op t1 t2) = do
     t1' <- go t1
     t2' <- go t2
     (tfTyInfix algebra) op t1' t2'

arity :: Type -> Nat
arity (FunTy _ t) = 1 + arity t
arity _           = 0

-- | Get the result type after the last Arrow, e.g. for @a -> b -> Pair a b@
-- the result type is @Pair a b@
resultType :: Type -> Type
resultType (FunTy _ t) = resultType t
resultType t = t


data Kind = KType
          | KCoeffect
          | KFun Kind Kind
          | KVar Id              -- Kind poly variable
          -- TODO: merge KType and KCoeffect into KConstr
          | KConstr Id           -- constructors
          | KPromote Type        -- Promoted types
    deriving (Show, Ord, Eq)

type Effect = [String]

data Coeffect = CNat      NatModifier Int
              | CNatOmega (Either () Int)
              | CFloat    Rational
              | CInfinity Type
              | CVar      Id
              | CPlus     Coeffect Coeffect
              | CTimes    Coeffect Coeffect
              | CMeet     Coeffect Coeffect
              | CJoin     Coeffect Coeffect
              | CZero     Type
              | COne      Type
              | Level     Int
              | CSet      [(String, Type)]
              | CSig      Coeffect Type
              | CExpon    Coeffect Coeffect
    deriving (Eq, Ord, Show)

data NatModifier = Ordered | Discrete
    deriving (Show, Ord, Eq)

-- | Normalise a coeffect using the semiring laws and some
--   local evaluation of natural numbers
--   There is plenty more scope to make this more comprehensive
normalise :: Coeffect -> Coeffect
normalise (CPlus (CZero _) n) = n
normalise (CPlus n (CZero _)) = n
normalise (CTimes (COne _) n) = n
normalise (CTimes n (COne _)) = n
normalise (COne (TyCon (Id _ "Nat"))) = CNat Ordered 1
normalise (CZero (TyCon (Id _ "Nat"))) = CNat Ordered 0
normalise (COne (TyCon (Id _ "Nat="))) = CNat Discrete 1
normalise (CZero (TyCon (Id _ "Nat="))) = CNat Discrete 0
normalise (COne (TyCon (Id _ "Level"))) = Level 1
normalise (CZero (TyCon (Id _ "Level"))) = Level 0
normalise (COne (TyCon (Id _ "Q"))) = CFloat 1
normalise (CZero (TyCon (Id _ "Q"))) = CFloat 0
normalise (CPlus (Level n) (Level m)) = Level (n `max` m)
normalise (CTimes (Level n) (Level m)) = Level (n `min` m)
normalise (CPlus (CFloat n) (CFloat m)) = CFloat (n + m)
normalise (CTimes (CFloat n) (CFloat m)) = CFloat (n * m)
normalise (CPlus (CNat k n) (CNat k' m)) | k == k' = CNat k (n + m)
normalise (CTimes (CNat k n) (CNat k' m)) | k == k' = CNat k (n * m)
normalise (CPlus n m) =
    if (n == n') && (m == m')
    then CPlus n m
    else normalise (CPlus n' m')
  where
    n' = normalise n
    m' = normalise m
normalise (CTimes n m) =
    if (n == n') && (m == m')
    then CTimes n m
    else normalise (CTimes n' m')
  where
    n' = normalise n
    m' = normalise m
normalise (CSig (CNat _ 0) k) = CZero k
normalise (CSig (CZero _)  k) = CZero k
normalise (CSig (CNat _ 1) k) = COne k
normalise (CSig (COne _)   k) = CZero k
normalise (CSig (CInfinity _)  k) = CInfinity k
normalise c = c
