{-# OPTIONS_GHC -Wno-unused-imports #-}

{-# LANGUAGE ScopedTypeVariables #-}

module Language.Granule.Synthesis.LinearHaskell where

import qualified Language.Granule.Syntax.Def as GrDef
import qualified Language.Granule.Syntax.Type as GrType
import qualified Language.Granule.Syntax.Identifiers as GrId
import qualified Language.Granule.Syntax.Expr as GrExpr
import qualified Language.Granule.Syntax.Pattern as GrPat
import qualified Language.Granule.Syntax.Pretty as GrP
import Language.Granule.Syntax.Span
import Language.Granule.Synthesis.Common
import Language.Granule.Synthesis.Synth
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Checker
import Language.Granule.Utils
import Language.Granule.Synthesis.RewriteHoles
import Language.Granule.Context

import Language.Granule.Checker.Checker

import Data.Maybe ( catMaybes )
import Data.Text (pack)
import qualified Data.Set as Set
import Debug.Trace
import Control.Monad ( foldM )
import Data.List (find, nub, reverse)
import Data.List.NonEmpty (NonEmpty, toList)
import qualified Data.List.NonEmpty as NonEmpty (filter)

import qualified Language.Haskell.Exts.Parser as Parser
import Language.Haskell.Exts.Parser
  ( ParseMode   ( .. )
  , defaultParseMode
  , ParseResult ( .. )
  )
import qualified Language.Haskell.Exts.Pretty as Pretty
import Language.Haskell.Exts.SrcLoc
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty

import Control.Exception (SomeException, displayException, try)



synthesiseLinearHaskell :: (?globals :: Globals) => GrDef.AST () () -> Module SrcSpanInfo -> IO (Maybe (Module SrcSpanInfo))
synthesiseLinearHaskell ast hsSrc = do
    checked <- try $ check ast
    case checked of
        Left (e :: SomeException) -> return Nothing
        Right (Left errs) -> do
            let holeErrs = getHoleMessages errs
            if length holeErrs == length errs && length holeErrs > 0 then do
                holes' <- synthLinearHoles holeErrs
                let holeCases = concatMap (\h -> map (\(pats, e) -> (errLoc h, zip (getCtxtIds (holeVars h)) pats, e)) (cases h)) holes'
                let ast' = holeRefactor holeCases ast
                let (relevantSpans, _, _) = unzip3 holeCases
                return $ Just $ exportHaskell relevantSpans ast' hsSrc
            else return Nothing
        _ -> return Nothing
    where

    getHoleMessages :: NonEmpty CheckerError -> [CheckerError]
    getHoleMessages es =
      NonEmpty.filter (\ e -> case e of HoleMessage{} -> True; _ -> False) es


synthLinearHoles :: (?globals :: Globals) => [CheckerError] -> IO [CheckerError]
synthLinearHoles [] = return []
synthLinearHoles ((HoleMessage sp goal ctxt tyVars holeVars synthCtxt@(Just (cs, defs, (Just defId, _), index, hints, constructors)) cases):holes) = do
    rest <- synthLinearHoles holes
    synRes <- synthesiseGradedBase hints index [] [] defId constructors ctxt (GrType.Forall nullSpan [] [] goal) cs
    case synRes of
        ([], _)    -> return $ HoleMessage sp goal ctxt tyVars holeVars synthCtxt cases : rest
        (res@(_:_), _) -> return $ HoleMessage sp goal ctxt tyVars holeVars synthCtxt [([], fst $ last $ res)] : rest
synthLinearHoles (hole:holes) = synthLinearHoles holes


writeHaskellToFile :: FilePath -> Module SrcSpanInfo -> IO ()
writeHaskellToFile path src = writeFile path $ prettyPrint src


exportHaskell :: [Span] -> GrDef.AST () () -> Module SrcSpanInfo -> Module SrcSpanInfo
exportHaskell = undefined

-- exportHaskell :: [(GrDef.Equation () (), SrcSpanInfo)] -> Module SrcSpanInfo -> Module SrcSpanInfo
-- exportHaskell eqs (Module spM modHead pragmas imports decls) =
--     Module spM modHead pragmas imports (replaceDecls decls eqs)

--     where

--     replaceDecls [] _ = []
--     replaceDecls ((FunBind sp matches):decls) eqs =
--         (FunBind sp (replaceMatches matches eqs)) : (replaceDecls decls eqs)
--     replaceDecls (p@(PatBind sp pat expr binds):decls) eqs =
--         let relEq = find (\(_, eSp) -> sp == eSp) eqs
--         in case relEq of
--             Just (GrDef.Equation _ _ _ _ _ grExpr, _) ->
--                 (PatBind sp pat (UnGuardedRhs noSrcSpan $ exprToHaskell grExpr) binds) : (replaceDecls decls eqs)
--             _ -> p : (replaceDecls decls eqs)
--     replaceDecls (decl:decls) eqs = decl : (replaceDecls decls eqs)

--     replaceMatches [] eqs = []
--     replaceMatches (m@(Match mSp name pats expr binds):matches) eqs =
--         let relEq = find (\(_, eSp) -> mSp == eSp) eqs
--         in case relEq of
--             Just (GrDef.Equation _ _ _ _ _ grExpr, _) ->
--                  (Match mSp name pats (UnGuardedRhs noSrcSpan $ exprToHaskell grExpr) binds) : (replaceMatches matches eqs)
--             _ -> m : (replaceMatches matches eqs)
--     replaceMatches (m:matches) eqs = m : (replaceMatches matches eqs)

-- exportHaskell _ _ = error "Not a Haskell Module"



{-

Import Linear Haskell to Granule
=================================

-}

processHaskell :: (?globals :: Globals) => FilePath -> IO (GrDef.AST () (), Module SrcSpanInfo)
processHaskell file = do
    contents <- readFile file
    let pResult   = Parser.parseModuleWithMode parseMode contents
        parseMode = defaultParseMode { parseFilename = file }
    case pResult of
        ParseOk hModule -> do
            ast <- toGranule hModule
            return (ast, hModule)
        ParseFailed _ err -> error $ "could not parse Haskell file " <> show err



toGranule :: (?globals :: Globals) => Module SrcSpanInfo -> IO (GrDef.AST () ())
toGranule src@(Module sp modHead pragmas imports decls) = do
    -- _ <- error $ show decls
    let (dataDecls, typeSchemes, funEqs) = foldl (\(datas, typeSchemes, funEqs) decl ->
            case decl of
                TypeSig{}   -> (datas, typeSigToGranule decl : typeSchemes, funEqs)
                FunBind{}   -> do
                    -- _ <- error $ show decl
                    (datas, typeSchemes, funBindToGranule decl : funEqs)
                DataDecl{}  -> (declToGranule decl : datas, typeSchemes, funEqs)
                GDataDecl{} -> (declToGranule decl : datas, typeSchemes, funEqs)
                _ -> (datas, typeSchemes, funEqs)
            ) ([], [], []) decls

    putStrLn $ "dataDecls: " <> GrP.pretty dataDecls
    putStrLn $ "funEqs: " <> GrP.pretty funEqs

    let (typeSchemes', tupDecls, usedList) = foldl (\(tys1, decls, usedList1) (tys2, usedList2, tups) ->
                let tys'   = tys1 ++ tys2
                    decls' = map tupDecl tups
                in (tys', decls' ++ decls, usedList1 || usedList2)
            ) ([], [], False) typeSchemes

    let dataDecls' = if usedList then listDecl : (nub tupDecls ++ catMaybes dataDecls) else (nub tupDecls ++ catMaybes dataDecls)

    let defDecls = foldl (\defs funEq ->
            case funEq of
                Just (funId, equationList) ->
                    case lookup funId typeSchemes' of
                        Just tySch -> (GrDef.Def ns funId False Nothing equationList tySch : defs)
                        Nothing -> defs
                Nothing -> defs
            ) [] funEqs

    putStrLn $ "defs: " <> show defDecls
    putStrLn $ "datas: " <> GrP.pretty dataDecls'

    return $ GrDef.AST dataDecls' defDecls mempty mempty Nothing
toGranule _ = error "file must be a Haskell module"


nameToGranule :: Name SrcSpanInfo -> GrId.Id
nameToGranule (Ident _ name)  = GrId.mkId name
nameToGranule (Symbol _ name) = GrId.mkId name



-- a Haskell type sig can have the form f,g :: a -> a which we need to turn into
-- (f, a -> a)
-- (g, a -> a)
-- to eventually pair each one with the relevant funBinds to make a Granule def
typeSigToGranule :: Decl SrcSpanInfo -> ([(GrId.Id, GrType.TypeScheme)], Bool, [Int])
typeSigToGranule (TypeSig sp ident ty) =
    let grTy = typeToGranule ty in
        case grTy of
            Just (grTy', usedList, tups) ->
                let tyVars = []
                in
                    (map (\ident' -> (nameToGranule ident', GrType.Forall (srcSpanInfoToGranule sp) tyVars [] grTy')) ident, usedList, tups)
            Nothing -> ([], False, [])
typeSigToGranule _ = ([], False, [])

typeToGranule :: Type SrcSpanInfo -> Maybe (GrType.Type, Bool, [Int])
typeToGranule (TyFun _ Nothing t1 t2) =
    let res1 = typeToGranule t1
        res2 = typeToGranule t2
    in case (res1, res2) of
        (Just (t1', ul1, tups1), Just (t2', ul2, tups2)) ->
            Just (GrType.FunTy Nothing (Just $ GrType.TyCon $ GrId.mkId "Many") t1' t2', ul1 || ul2, tups1 ++ tups2)
        _ -> Nothing
typeToGranule (TyFun _ (Just (TyCon _ (UnQual _ (Ident _ name)))) t1 t2) | name == "->." =
    let res1 = typeToGranule t1
        res2 = typeToGranule t2
    in case (res1, res2) of
        (Just (t1', ul1, tups1), Just (t2', ul2, tups2)) ->
            Just (GrType.FunTy Nothing (Just $ GrType.TyCon $ GrId.mkId "One") t1' t2', ul1 || ul2, tups1 ++ tups2)
        _ -> Nothing
typeToGranule (TyFun _ (Just mult) t1 t2) =
    let res1     = typeToGranule t1
        res2     = typeToGranule t2
        resMult  = typeToGranule mult
    in case (res1, res2, resMult) of
        (Just (t1', ul1, tups1), Just (t2', ul2, tups2), Just (mult', _, _)) ->
            Just (GrType.FunTy Nothing (Just mult') t1' t2', ul1 || ul2, tups1 ++ tups2)
        _ -> Nothing
typeToGranule (TyStar _) =
    Just (GrType.Type 0, False, [])
typeToGranule (TyCon _ (UnQual _ name)) =
    Just (GrType.TyCon $ nameToGranule name, False, [])
typeToGranule (TyApp _ t1 t2) =
    let res1 = typeToGranule t1
        res2 = typeToGranule t2
    in case (res1, res2) of
        (Just (t1', ul1, tups1), Just (t2', ul2, tups2)) ->
            Just (GrType.TyApp t1' t2', ul1 || ul2, tups1 ++ tups2)
        _ -> Nothing
typeToGranule (TyVar _ name) =
    Just (GrType.TyVar $ nameToGranule name, False, [])
typeToGranule (TyParen _ t) = typeToGranule t
typeToGranule (TyList _ t) =
    let res = typeToGranule t
    in case res of
        Just (t', _, tups) -> Just (GrType.TyApp (GrType.TyCon $ GrId.mkId "#List") t', True, tups)
        Nothing -> Nothing
typeToGranule (TyTuple _ _ tys) =
    case buildType (reverse tys) $ GrType.TyCon $ GrId.mkId $ "," <> (show $ length tys) of
        Just (ty, ul, tups) -> Just (ty, ul, length tys : tups)
        Nothing -> Nothing
    where

        buildType [] tupTy = Just (tupTy, False, [])
        buildType (t1:ts) tupTy =
            let res1 = buildType ts tupTy
                res2 = typeToGranule t1
            in case (res1, res2) of
                (Just (t2, ul, tups), Just (t1', ul', tups')) -> Just (GrType.TyApp t2 t1', ul || ul', tups ++ tups')
                _ -> Nothing

-- If we cannot find out what a Granule equivalent type is, then just ignore it rather than error out
typeToGranule _ = Nothing


-- Translating a Decl into Granule is a bit tricky. The code here
-- is extremely rudimentary.
-- Uneasy about the generous use of catMaybes in declToGranule and conToGranule.
-- Wouldn't it be better to not translate the entire DataDecl (+ any types that)
-- make use of it, rather than translate it partially?
declToGranule :: Decl SrcSpanInfo -> Maybe (GrDef.DataDecl)
declToGranule (DataDecl sp (DataType _) _ dhead cons _) = do
    (grId, tyVarCtxt) <- dheadToGranule dhead
    return $ GrDef.DataDecl (srcSpanInfoToGranule sp) grId tyVarCtxt Nothing $ catMaybes $ map conToGranule cons
declToGranule (GDataDecl sp (DataType _) _ dhead (Just kind) gCons _) = do
    (grId, tyVarCtxt) <- dheadToGranule dhead
    (kind', _, _) <- typeToGranule kind
    return $ GrDef.DataDecl (srcSpanInfoToGranule sp) grId tyVarCtxt (Just kind') $ catMaybes $ map gConToGranule gCons
declToGranule (GDataDecl sp (DataType _) _ dhead Nothing gCons _) = do
    (grId, tyVarCtxt) <- dheadToGranule dhead
    return $ GrDef.DataDecl (srcSpanInfoToGranule sp) grId tyVarCtxt Nothing $ catMaybes $ map gConToGranule gCons
declToGranule _ = Nothing


dheadToGranule :: DeclHead SrcSpanInfo -> Maybe (GrId.Id, [(GrId.Id, GrType.Kind)])
dheadToGranule (DHead _ name) = Just (nameToGranule name, [])
dheadToGranule (DHParen _ dhead) = dheadToGranule dhead
dheadToGranule (DHApp _ dhead bind) = do
    (dId, binds) <- dheadToGranule dhead
    bind' <- bindToGranule bind
    return (dId, bind':binds)
dheadToGranule (DHInfix _ binds name) = Nothing


bindToGranule :: TyVarBind SrcSpanInfo -> Maybe (GrId.Id, GrType.Kind)
bindToGranule (UnkindedVar _ name)    = Just (nameToGranule name, GrType.Type 0)
-- TODO work out how to translate Haskell kinds into Granule properly
bindToGranule (KindedVar _ name kind) = do
    (kind', _, _) <- typeToGranule kind
    Just (nameToGranule name, kind')


gConToGranule :: GadtDecl SrcSpanInfo -> Maybe (GrDef.DataConstr)
gConToGranule (GadtDecl sp name Nothing _ _ ty) = do
    (ty', _, _) <- typeToGranule ty
    Just $ GrDef.DataConstrIndexed (srcSpanInfoToGranule sp) (nameToGranule name) (GrType.Forall ns [] [] ty')
gConToGranule (GadtDecl sp name (Just existentials) _ _ ty) = do
    let binders  = catMaybes $ map bindToGranule existentials
    (ty', _, _) <- typeToGranule ty
    Just $ GrDef.DataConstrIndexed (srcSpanInfoToGranule sp) (nameToGranule name) (GrType.Forall ns binders [] ty')


conToGranule :: QualConDecl SrcSpanInfo -> Maybe (GrDef.DataConstr)
conToGranule (QualConDecl sp Nothing _ (ConDecl _ name args)) =
    -- TODO: Work out how to handle if lists or tuples occur inside a data con parameter
    let tys = map (typeToGranule) args
        tys' = map fst3 $ catMaybes tys
    in Just $ GrDef.DataConstrNonIndexed (srcSpanInfoToGranule sp) (nameToGranule name) tys'
-- I don't like this case. Why are we trying to introduce an Indexed data con just
-- because we have a typescheme in the source. What would be the best way to handle
-- this? Just ignore the source binds?
conToGranule (QualConDecl sp (Just existentials) _ (ConDecl _ name args)) =
    let binders  = catMaybes $ map bindToGranule existentials
        tys      = map (typeToGranule) args
        tys'     = map fst3 $ catMaybes tys
        funTy    = makeFunTy tys'
    in case funTy of
        Just ty -> Just $ GrDef.DataConstrIndexed (srcSpanInfoToGranule sp) (nameToGranule name) (GrType.Forall ns binders [] ty)
        Nothing -> Nothing

    where
        makeFunTy :: [GrType.Type] -> Maybe GrType.Type
        makeFunTy [] = Nothing
        makeFunTy [t] = Just t
        makeFunTy (t:ts) = do
            t' <- makeFunTy ts
            Just $ GrType.funTy t t'

conToGranule _ = Nothing


listDecl :: GrDef.DataDecl
listDecl =
    GrDef.DataDecl {
        GrDef.dataDeclSpan = ns,
        GrDef.dataDeclId = GrId.mkId "#List",
        GrDef.dataDeclTyVarCtxt = [((GrId.Id "a" "a"), GrType.Type 0)],
        GrDef.dataDeclKindAnn = Nothing,
        GrDef.dataDeclDataConstrs = [
            GrDef.DataConstrNonIndexed {
                GrDef.dataConstrSpan = ns,
                GrDef.dataConstrId = GrId.mkId "[]",
                GrDef.dataConstrParams = []
                },
        GrDef.DataConstrNonIndexed {
            GrDef.dataConstrSpan = ns,
            GrDef.dataConstrId = GrId.mkId ":",
            GrDef.dataConstrParams = [ GrType.TyVar $ GrId.mkId "a", GrType.TyApp (GrType.TyCon $ GrId.mkId "#List") (GrType.TyVar $ GrId.mkId "a") ]
            }
        ]}

tupDecl :: Int -> GrDef.DataDecl
tupDecl n =
    let tyVarNames = "abcdefghijkl"
        tyVars = map GrId.mkId (map (: []) (take n tyVarNames)) in
    GrDef.DataDecl {
        GrDef.dataDeclSpan = ns,
        GrDef.dataDeclId = GrId.mkId $ "," <> (show n),
        GrDef.dataDeclTyVarCtxt = map (\tyVar -> (tyVar, GrType.Type 0)) tyVars,
        GrDef.dataDeclKindAnn = Just (GrType.Type 0),
        GrDef.dataDeclDataConstrs = [
            GrDef.DataConstrNonIndexed {
                GrDef.dataConstrSpan = ns,
                GrDef.dataConstrId = GrId.mkId $ "," <> (show n),
                GrDef.dataConstrParams = map (\tyVar -> GrType.TyVar tyVar) tyVars
                }
            ]}




-- TODO we should be using the Match srcSpanInfo here to pass to the synth hole
-- otherwise we cannot synthesise two holes with different patterns for the same
-- funBind e.g.
-- f (x, y) = _
-- f x = _
funBindToGranule :: Decl SrcSpanInfo -> Maybe (GrId.Id, GrDef.EquationList () ())
funBindToGranule (FunBind _ matches) =
    let (eqs, grId) = matchesToGranule matches
    in
        case grId of
            Just id -> Just (id, GrDef.EquationList ns id False eqs)
            Nothing -> error "not sure how this happened :|"
    where
        matchesToGranule ((Match sp name pats rhs whereBinds):matches) = --  error "I got here"

            let (grEqs, _) = matchesToGranule matches
                -- grLet      = bindsToGranule
                grId       = nameToGranule name
                grPats     = catMaybes $ map patternToGranule pats
                grExpr     =
                    case rhsToGranule rhs of
                        Just rhs' -> exprToGranule rhs' (srcSpanInfoToGranule sp)
                        Nothing   -> Just $ GrExpr.Hole ns () False [] Nothing
            in case grExpr of
                Just grExpr' -> ((GrDef.Equation (srcSpanInfoToGranule sp) grId () False grPats grExpr') : grEqs, Just grId)
                _ -> (grEqs, Just grId)

        -- Skip over infix matches for now
        matchesToGranule ((InfixMatch{}):matches) = matchesToGranule matches
        matchesToGranule [] = ([], Nothing)

-- Should never be reached
funBindToGranule _ = error "We only consider funBinds or patBinds for translation"


-- Functions with no patterns (e.g. f = _) get parsed as PatBinds
patBindToGranule :: Decl SrcSpanInfo -> Maybe (GrId.Id, GrDef.EquationList () ())
patBindToGranule (PatBind s (PVar _ hsName) rhs _) = do
    hsExpr <- rhsToGranule rhs
    grExpr <- exprToGranule hsExpr (srcSpanInfoToGranule s)
    let grName = nameToGranule hsName
        grEqs   = GrDef.EquationList ns grName False [GrDef.Equation ns grName () False [] grExpr]
    return (grName, grEqs)
patBindToGranule _ = Nothing


rhsToGranule :: Rhs SrcSpanInfo -> Maybe (Exp SrcSpanInfo)
rhsToGranule (UnGuardedRhs _ expr) = Just expr
-- I don't know how to deal with guards, so just ignore this.
rhsToGranule _ = Nothing


-- Translate a Haskell span into a Granule one so that we know which holes to synth on.
-- The Span is that of the FunBind (should be the Match, see comment above funBindToGranule)
srcSpanInfoToGranule :: SrcSpanInfo -> Span
srcSpanInfoToGranule (SrcSpanInfo (SrcSpan fn sl sc el ec) _) =
    Span { startPos = (sl, sc), endPos = (el, ec), filename = fn}

spanToHaskell :: Span -> SrcSpanInfo
spanToHaskell (Span (sl, sc) (el, ec) fn) = SrcSpanInfo (SrcSpan fn sl sc el ec) []


-- At the moment we only convert typed holes that are at the top-level of the rhs in a funBind
exprToGranule :: Exp SrcSpanInfo -> Span -> Maybe (GrExpr.Expr () ())
exprToGranule (Con sp (Special _ (ExprHole _))) loc =
    let hints = GrExpr.Hints False False False False (Just loc) Nothing Nothing
    in Just $ GrExpr.Hole (srcSpanInfoToGranule sp) () False [] (Just $ hints)
exprToGranule (Var _ (Special _ (ExprHole _))) loc =
    let hints = GrExpr.Hints False False False False (Just loc) Nothing Nothing
    in Just $ GrExpr.Hole ns () False [] (Just $ hints)
exprToGranule e _                 = Nothing -- error $ show e

literalToGranule :: Literal SrcSpanInfo -> Maybe (GrExpr.Value () ())
literalToGranule (Char _ char _)            = Just $ GrExpr.CharLiteral char
literalToGranule (String _ string _)        = Just $ GrExpr.StringLiteral $ pack string
literalToGranule (Int _ int _)              = Just $ GrExpr.NumInt $ fromInteger int
literalToGranule (PrimInt _ pint _)         = Just $ GrExpr.NumInt $ fromInteger pint
literalToGranule (PrimFloat _ pfloat _)     = Just $ GrExpr.NumFloat $ fromRational pfloat
literalToGranule (PrimChar _ pchar _)       = Just $ GrExpr.CharLiteral pchar
literalToGranule (PrimString _ pstring _)   = Just $ GrExpr.StringLiteral $ pack pstring
literalToGranule _                          = Nothing


patternToGranule :: Pat SrcSpanInfo -> Maybe (GrPat.Pattern ())
patternToGranule (PVar _ name) = Just $ GrPat.PVar ns () False $ nameToGranule name
patternToGranule (PLit _ sign (Int _ int _)) = Just $ GrPat.PInt ns () False $ fromInteger int
patternToGranule (PParen _ p) = patternToGranule p
patternToGranule (PWildCard _) = Just $ GrPat.PWild ns () False
patternToGranule (PTuple _ _ ps) =
     -- the tuple must be in our defined decls so we can just match on the correct Con
    let ps'   = catMaybes $ map patternToGranule ps
        tupId = GrId.mkId $ "," <> (show $ length ps)
    in Just $ GrPat.PConstr ns () False tupId ps'
patternToGranule (PApp _ (UnQual _ name) ps) =
    let ps'   = catMaybes $ map patternToGranule ps
        conId = nameToGranule name
    in Just $ GrPat.PConstr ns () False conId ps'
patternToGranule _ = Nothing







patternToHaskell :: GrPat.Pattern () -> Pat SrcSpanInfo
patternToHaskell (GrPat.PVar _ _ _ i)   = PVar noSrcSpan $ idToHaskell i
patternToHaskell (GrPat.PWild{})        = PWildCard noSrcSpan
patternToHaskell (GrPat.PBox _ _ _ pt)  = patternToHaskell pt
patternToHaskell (GrPat.PInt _ _ _ n)   = PLit noSrcSpan (Signless noSrcSpan) $ Int noSrcSpan (fromIntegral n) (show n)
patternToHaskell (GrPat.PFloat _ _ _ n) = PLit noSrcSpan (Signless noSrcSpan) $ Frac noSrcSpan (toRational n) (show n)
patternToHaskell (GrPat.PConstr _ _ _ id@(GrId.Id _ i) l_pt)
  | ',' `elem` i = PTuple noSrcSpan Boxed $ map patternToHaskell l_pt
  | otherwise = PApp noSrcSpan (UnQual noSrcSpan $ idToHaskell id) $ map patternToHaskell l_pt


exprToHaskell :: GrExpr.Expr () () -> Exp SrcSpanInfo
exprToHaskell (GrExpr.App _ _ _ e1 e2) =
    let (leftMostExpr, args) = leftMostAndArgs e1
    in if isTupleExpr leftMostExpr
    then Tuple noSrcSpan Boxed $ map exprToHaskell (e2:args)
    else
        let e1' = exprToHaskell e1
            e2' = exprToHaskell e2
        in App noSrcSpan e1' e2'
    where
        leftMostAndArgs (GrExpr.App _ _ _ e1 e2) =
            let (e1', args) = leftMostAndArgs e1
            in (e1', e2:args)
        leftMostAndArgs e = (e, [])

        isTupleExpr (GrExpr.Val _ _ _ (GrExpr.Constr _ (GrId.Id _ i) _ )) | ',' `elem` i = True
        isTupleExpr _ = False
exprToHaskell (GrExpr.Binop _ _ _ op e1 e2) =
    let e1' = exprToHaskell e1
        e2' = exprToHaskell e2
    in
        binopToHaskell op e1' e2'
exprToHaskell (GrExpr.LetDiamond _ _ _ p _ e1 e2) =
    let p'  = patternToHaskell p
        e1' = exprToHaskell e1
        e2' = exprToHaskell e2
        lam = Lambda noSrcSpan [p'] e2'
    in
        InfixApp noSrcSpan e1' (QVarOp noSrcSpan . UnQual noSrcSpan $ Symbol noSrcSpan ">>=") lam
exprToHaskell (GrExpr.Val _ _ _ v) = valToHaskell v
exprToHaskell (GrExpr.Case _ _ _ ge cases) =
    let ge'    = exprToHaskell ge
        alt'    = \p e -> Alt noSrcSpan p (UnGuardedRhs noSrcSpan e) Nothing
        cases' = map (\(p, e) -> let (p', e') = (patternToHaskell p, exprToHaskell e) in alt' p' e') cases
    in Case noSrcSpan ge' cases'
exprToHaskell (GrExpr.Hole _ _ _ e1 e2) =  (Con noSrcSpan (Special noSrcSpan (ExprHole noSrcSpan)))
exprToHaskell expr = error ("I can't convert this expression to Haskell: " <> show expr)





valToHaskell :: GrExpr.Value () () -> Exp SrcSpanInfo
valToHaskell (GrExpr.Constr _ id vals) =
    let vals' = map valToHaskell vals
        name  = idToHaskell id
        con   = Con noSrcSpan (UnQual noSrcSpan name)
    in appFun con vals'
    where
        appFun f [] = f
        appFun f (a:as) = appFun (App noSrcSpan f a) as
valToHaskell (GrExpr.Var _ id) = Var noSrcSpan (UnQual noSrcSpan $ idToHaskell id)
valToHaskell (GrExpr.Abs _ p _ e) =
    let p' = patternToHaskell p
        e' = exprToHaskell e
    in Lambda noSrcSpan [p'] e'
valToHaskell (GrExpr.CharLiteral char)   = Lit noSrcSpan $ Char noSrcSpan char (show char)
valToHaskell (GrExpr.NumInt int)         = Lit noSrcSpan $ Int noSrcSpan (fromIntegral int) (show int)
valToHaskell val = error ("Not sure how to handle this yet!" <> show val)


binopToHaskell :: GrExpr.Operator -> Exp SrcSpanInfo -> Exp SrcSpanInfo -> Exp SrcSpanInfo
binopToHaskell GrExpr.OpLesser e1 e2    = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan "<"))) e2
binopToHaskell GrExpr.OpLesserEq e1 e2  = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan "<="))) e2
binopToHaskell GrExpr.OpGreater e1 e2   = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan ">"))) e2
binopToHaskell GrExpr.OpGreaterEq e1 e2 = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan ">="))) e2
binopToHaskell GrExpr.OpEq e1 e2        = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan "=="))) e2
binopToHaskell GrExpr.OpNotEq e1 e2     = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan "/="))) e2
binopToHaskell GrExpr.OpPlus e1 e2      = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan "+"))) e2
binopToHaskell GrExpr.OpTimes e1 e2     = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan "*"))) e2
binopToHaskell GrExpr.OpDiv e1 e2       = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan "/"))) e2
binopToHaskell GrExpr.OpMinus e1 e2     = InfixApp noSrcSpan e1 (QVarOp noSrcSpan (UnQual noSrcSpan (Symbol noSrcSpan "-"))) e2


idToHaskell :: GrId.Id -> Name SrcSpanInfo
idToHaskell (GrId.Id _ i) = (Ident noSrcSpan i)

