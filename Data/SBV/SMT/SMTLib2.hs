----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMTLib2
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Conversion of symbolic programs to SMTLib format, Using v2 of the standard
-----------------------------------------------------------------------------
{-# LANGUAGE PatternGuards #-}

module Data.SBV.SMT.SMTLib2(cvt, addNonEqConstraints) where

import Data.Bits     (bit)
import Data.Function (on)
import Data.Ord      (comparing)
import Data.List     (partition, groupBy, sortBy)

import qualified Data.Map      as M
import qualified Data.IntMap   as IM
import qualified Data.Set      as Set

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (smtRoundingMode, cwToSMTLib)

import Data.SBV.SMT.Script

-- | Add constraints to generate /new/ models. This function is used to query the SMT-solver, while
-- disallowing a previous model.
addNonEqConstraints :: RoundingMode -> [(Quantifier, NamedSymVar)] -> [[(String, CW)]] -> SMTLibPgm -> Maybe String
addNonEqConstraints rm qinps allNonEqConstraints pgm@(SMTLibPgm _ (aliasTable, pre, post))
  | null allNonEqConstraints
  = Just $ show pgm
  | null refutedModel
  = Nothing
  | True
  = Just $ render $  pre
                  $$ text "; --- refuted-models ---"
                  $$ vcat refutedModel
                  $$ post
 where refutedModel = concatMap (nonEqs rm . map intName) nonEqConstraints
       intName (s, c)
          | Just sw <- s `lookup` aliasTable = (show sw, c)
          | True                             = (s, c)
       -- with existentials, we only add top-level existentials to the refuted-models list
       nonEqConstraints = filter (not . null) $ map (filter (\(s, _) -> s `elem` topUnivs)) allNonEqConstraints
       topUnivs = [s | (_, (_, s)) <- takeWhile (\p -> fst p == EX) qinps]

nonEqs :: RoundingMode -> [(String, CW)] -> [Script]
nonEqs rm scs = format $ interp ps ++ disallow (map eqClass uninterpClasses)
  where isFree (KUserSort _ (Left _)) = True
        isFree _                      = False
        (ups, ps) = partition (isFree . kindOf . snd) scs
        format []  =  []
        format [m] =  [parens (text "assert" <+> m)]
        format ms  =  [parens (text "assert" <+> parens (text "or" <+> vcat ms))]
        -- Regular (or interpreted) sorts simply get a constraint that we disallow the current assignment
        interp = map $ nonEq rm
        -- Determine the equivalence classes of uninterpreted sorts:
        uninterpClasses = filter (\l -> length l > 1) -- Only need this class if it has at least two members
                        . map (map fst)               -- throw away sorts, we only need the names
                        . groupBy ((==) `on` snd)     -- make sure they belong to the same sort and have the same value
                        . sortBy (comparing snd)      -- sort them according to their sorts first
                        $ ups                         -- take the uninterpreted sorts
        -- Uninterpreted sorts get a constraint that says the equivalence classes as determined by the solver are disallowed:
        eqClass :: [String] -> Script
        eqClass [] = error "SBV.allSat.nonEqs: Impossible happened, disallow received an empty list"
        eqClass cs = parens (text "=" <+> hsep (map text cs))
        -- Now, take the conjunction of equivalence classes and assert it's negation:
        disallow = map $ \ec -> parens (text "not" <+> ec)

nonEq :: RoundingMode -> (String, CW) -> Script
nonEq rm (s, c) = parens (text "not" <+> parens (text "=" <+> text s <+> cvtCW rm c))

tbd :: String -> a
tbd e = error $ "SBV.SMTLib2: Not-yet-supported: " ++ e

-- | Translate a problem into an SMTLib2 script
cvt :: RoundingMode                 -- ^ User selected rounding mode to be used for floating point arithmetic
    -> Maybe Logic                  -- ^ SMT-Lib logic, if requested by the user
    -> SolverCapabilities           -- ^ capabilities of the current solver
    -> Set.Set Kind                 -- ^ kinds used
    -> Bool                         -- ^ is this a sat problem?
    -> [String]                     -- ^ extra comments to place on top
    -> [(Quantifier, NamedSymVar)]  -- ^ inputs
    -> [Either SW (SW, [SW])]       -- ^ skolemized version inputs
    -> [(SW, CW)]                   -- ^ constants
    -> [((Int, Kind, Kind), [SW])]  -- ^ auto-generated tables
    -> [(Int, ArrayInfo)]           -- ^ user specified arrays
    -> [(String, SBVType)]          -- ^ uninterpreted functions/constants
    -> [(String, [String])]         -- ^ user given axioms
    -> SBVPgm                       -- ^ assignments
    -> [SW]                         -- ^ extra constraints
    -> SW                           -- ^ output variable
    -> (Script, Script)
cvt rm smtLogic solverCaps kindInfo isSat comments inputs skolemInps consts tbls arrs uis axs (SBVPgm asgnsSeq) cstrs out = (script, post)
  where post           = empty

        hasInteger     = KUnbounded `Set.member` kindInfo
        hasReal        = KReal      `Set.member` kindInfo
        hasFloat       = KFloat     `Set.member` kindInfo
        hasDouble      = KDouble    `Set.member` kindInfo
        hasBVs         = not $ null [() | KBounded{} <- Set.toList kindInfo]
        usorts         = [(s, dt) | KUserSort s dt <- Set.toList kindInfo]
        hasNonBVArrays = (not . null) [() | (_, (_, (k1, k2), _)) <- arrs, not (isBounded k1 && isBounded k2)]
        foralls        = [s | Left s <- skolemInps]
        hasForAlls     = not $ null foralls

        -- Determine the logic. This is necessarily an over-approximation
        logic
           | Just l <- smtLogic
           = sl (show l) (Just "NB. User specified.")
           | hasDouble || hasFloat    -- NB. We don't check for quantifiers here, we probably should..
           = if hasBVs
             then sl "QF_FPBV" Nothing
             else sl "QF_FP"   Nothing
           | hasInteger || hasReal || not (null usorts) || hasNonBVArrays
           = let why | hasInteger        = "has unbounded values"
                     | hasReal           = "has algebraic reals"
                     | not (null usorts) = "has user-defined sorts"
                     | hasNonBVArrays    = "has non-bitvector arrays"
                     | True              = "cannot determine the SMTLib-logic to use"
             in case mbDefaultLogic solverCaps hasReal of
                  Nothing -> text "; " <+>  text why <> text ", no logic specified."
                  Just l  -> sl l $ Just $ why ++ ", using solver-default logic."
           | True
           = sl (qs ++ as ++ ufs ++ "BV") Nothing
          where sl l (Just c) = parens (text "set-logic" <+> text l) <+> text ";" <+> text c
                sl l Nothing  = parens (text "set-logic" <+> text l)

                qs  | hasForAlls && null axs = "QF_"  -- axioms are likely to contain quantifiers
                    | True                     = ""
                as  | null arrs                = ""
                    | True                     = "A"
                ufs | null uis && null tbls    = ""     -- we represent tables as UFs
                    | True                     = "UF"

        getModels
          | supportsProduceModels solverCaps = text "(set-option :produce-models true)"
          | True                             = empty

        script :: Script
        script =  text "; Automatically generated by SBV. Do not edit."
               $$ vcat (map (\c -> text "; " <+> text c) comments)
               $$ getModels
               $$ logic
               $$ text "; --- uninterpreted sorts ---"
               $$ vcat (map declSort usorts)
               $$ text "; --- literal constants ---"
               $$ vcat (map (declConst (supportsMacros solverCaps)) consts)
               $$ text "; --- skolem constants ---"
               $$ vcat [ parens (text "declare-fun" <+> text (show s) <+> swFunType ss s) <+> userName s | Right (s, ss) <- skolemInps]
               $$ text "; --- constant tables ---"
               $$ vcat (map constTable constTables)
               $$ text "; --- skolemized tables ---"
               $$ vcat (map (skolemTable (map swType foralls)) skolemTables)
               $$ text "; --- arrays ---"
               $$ vcat arrayConstants
               $$ text "; --- uninterpreted constants ---"
               $$ vcat (map declUI uis)
               $$ text "; --- user given axioms ---"
               $$ vcat (map declAx axs)
               $$ text "; --- formula ---"
               $$ parens (text "assert" <+> quantifiedScriptBody)

        quantifiedScriptBody
          | not hasForAlls =   text "; no quantifiers"
                            $$ smt2Script
          | True           =   parens (   text "forall" <+> parens (hsep (map qvar foralls))
                                       $$ smt2Script)
          where qvar s = text (show s) <+> swType s

        smt2Script = foldr glue final asgnsSeq
         where final
                 | null delayed = assertOut
                 | True         = parens (hang (text "and") 4 (hsep delayed $$ assertOut))
               glue :: (SW, SBVExpr) -> Script -> Script
               glue (s, SBVApp (Label m) [e]) rest = parens (hang (text "let" <+> parens (parens (text (show s) <+> cvtSW     skolemMap          e)) <+> text ("; " ++ m)) (-1) rest)
               glue (s, e)                    rest = parens (hang (text "let" <+> parens (parens (text (show s) <+> cvtExp rm skolemMap tableMap e))                     ) (-1) rest)

        allTables    = [(t, genTableData rm skolemMap (not hasForAlls, foralls) (map fst consts) t) | t <- tbls]
        constTables  = [(t, d) | (t, Left  d) <- allTables]
        skolemTables = [(t, d) | (t, Right d) <- allTables]

        (arrayConstants, allArrayDelayeds) = unzip $ map (declArray (not hasForAlls) (map fst consts) skolemMap) arrs

        delayed = concatMap snd skolemTables ++ allArrayDelayeds

        -- if sat,   we assert cstrs /\ out
        -- if prove, we assert ~(cstrs => out) = cstrs /\ not out
        assertOut
           | null cstrs = o
           | True       = parens (text "and" <+> hsep (map mkConj cstrs) <+> o)
           where mkConj = cvtSW skolemMap
                 o | isSat =                        mkConj out
                   | True  = parens (text "not" <+> mkConj out)

        skolemMap = M.fromList [(s, ss) | Right (s, ss) <- skolemInps, not (null ss)]

        tableMap  = IM.fromList $ map mkConstTable constTables ++ map mkSkTable skolemTables
          where mkConstTable (((t, _, _), _), _) = (t, text ("table" ++ show t))
                mkSkTable    (((t, _, _), _), _) = (t, text ("table" ++ show t ++ " " ++ unwords (map show foralls)))

        declConst :: Bool -> (SW, CW) -> Script
        declConst useDefFun (s, c)
          | useDefFun = parens (text "define-fun"  <+> varT <+> cvtCW rm c)
          | True      =  parens (text "declare-fun" <+> varT)
                      $$ parens (text "assert" <+> parens (text "=" <+> text (show s) <+> cvtCW rm c))
          where varT = text (show s) <+> swFunType [] s

        userName s = case s `lookup` map snd inputs of
                        Just u  | show s /= u -> text $ " ; tracks user variable " ++ show u
                        _ -> empty

        -- following sorts are built-in; do not translate them:
        builtInSort = (`elem` ["RoundingMode"])
        declSort :: (String, Either String [String]) -> Script
        declSort (s, _)
          | builtInSort s      = empty
        declSort (s, Left  r ) = parens (text "declare-sort" <+> text (s ++ " 0")) <+> text (" ; N.B. Uninterpreted: " ++ r)
        declSort (s, Right fs) =  parens (text "declare-datatypes" <+> text "()" <+> parens (parens (text s <+> hsep (map (parens . text) fs))))
                               $$ parens (   text "define-fun " <+> (   text (s ++ "_constrIndex") <+> parens (parens (text "x" <+> text s)) <+> text "Int"
                                                                     $$ body fs (0::Int)))
                where body []     _ = empty
                      body [_]    i = int i
                      body (c:cs) i = parens (text "ite" <+> parens (text "= x" <+> text c) <+> int i <+> body cs (i+1))

declUI :: (String, SBVType) -> Script
declUI (i, t) = parens (text "declare-fun" <+> text i <+> cvtType t)

-- NB. We perform no check to as to whether the axiom is meaningful in any way.
declAx :: (String, [String]) -> Script
declAx (nm, ls) =  (text ";; -- user given axiom: " <+> text nm)
                $$ vcat (map text ls)

constTable :: (((Int, Kind, Kind), [SW]), [Script]) -> Script
constTable (((i, ak, rk), _elts), is) = vcat (decl : map wrap is)
  where t       = text ("table" ++ show i)
        decl    = parens (text "declare-fun" <+> t <+> parens (smtType ak) <+> smtType rk)
        wrap  s = parens (text "assert" <+> s)

skolemTable :: [Script] -> (((Int, Kind, Kind), [SW]), [Script]) -> Script
skolemTable qs (((i, ak, rk), _elts), _) = decl
  where t    = text ("table" ++ show i)
        decl = parens (text "declare-fun" <+> t <+> parens (hsep qs <+> smtType ak) <+> smtType rk)

-- Left if all constants, Right if otherwise
genTableData :: RoundingMode -> SkolemMap -> (Bool, [SW]) -> [SW] -> ((Int, Kind, Kind), [SW]) -> Either [Script] [Script]
genTableData rm skolemMap (_quantified, args) consts ((i, aknd, _), elts)
  | null post = Left  (map (topLevel . snd) pre)
  | True      = Right (map (nested   . snd) (pre ++ post))
  where ssw = cvtSW skolemMap
        (pre, post) = partition fst (zipWith mkElt elts [(0::Int)..])
        t           = text ("table" ++ show i)
        mkElt x k   = (isReady, (idx, ssw x))
          where idx = cvtCW rm (mkConstCW aknd k)
                isReady = x `elem` consts
        topLevel (idx, v) = parens (text "=" <+> parens (t <+>                                  idx) <+> v)
        nested   (idx, v) = parens (text "=" <+> parens (t <+> hsep (map (text . show) args) <+> idx) <+> v)

-- TODO: We currently do not support non-constant arrays when quantifiers are present, as
-- we might have to skolemize those. Implement this properly.
-- The difficulty is with the ArrayReset/Mutate/Merge: We have to postpone an init if
-- the components are themselves postponed, so this cannot be implemented as a simple map.
declArray :: Bool -> [SW] -> SkolemMap -> (Int, ArrayInfo) -> (Script, Script)
declArray quantified consts skolemMap (i, (_, (aKnd, bKnd), ctx)) = (vcat (adecl : map wrap pre), vcat (map snd post))
  where topLevel = not quantified || case ctx of
                                       ArrayFree Nothing -> True
                                       ArrayFree (Just sw) -> sw `elem` consts
                                       ArrayReset _ sw     -> sw `elem` consts
                                       ArrayMutate _ a b   -> all (`elem` consts) [a, b]
                                       ArrayMerge c _ _    -> c `elem` consts
        (pre, post) = partition fst ctxInfo
        nm = "array_" ++ show i
        ssw sw
         | topLevel || sw `elem` consts
         = cvtSW skolemMap sw
         | True
         = tbd "Non-constant array initializer in a quantified context"
        adecl = parens (text "declare-fun" <+> text nm <+> text "()" <+> parens (text "Array" <+> smtType aKnd <+> smtType bKnd))
        ctxInfo = case ctx of
                    ArrayFree Nothing   -> []
                    ArrayFree (Just sw) -> declA sw
                    ArrayReset _ sw     -> declA sw
                    ArrayMutate j a b   -> let aj = text ("array_" ++ show j)
                                           in [(all (`elem` consts) [a, b], parens (text "=" <+> text nm <+> parens (text "store" <+> aj <+> ssw a <+> ssw b)))]
                    ArrayMerge  t j k   -> let aj = text ("array_" ++ show j)
                                               ak = text ("array_" ++ show k)
                                           in [(t `elem` consts,            parens (text "=" <+> text nm <+> parens (text "ite" <+> ssw t <+> aj <+> ak)))]
        declA sw = let iv = text $ nm ++ "_freeInitializer"
                   in [ (True,             parens (text "declare-fun" <+> iv <+> text "()" <+> smtType aKnd))
                      , (sw `elem` consts, parens (text "=" <+> parens (text "select" <+> text nm <+> iv) <+> ssw sw))
                      ]
        wrap (False, s) = s
        wrap (True,  s) = parens (text "assert" <+> s)

swType :: SW -> Script
swType s = smtType (kindOf s)

swFunType :: [SW] -> SW -> Script
swFunType ss s = parens (hsep (map swType ss)) <+> swType s

smtType :: Kind -> Script
smtType KBool           = text   "Bool"
smtType (KBounded _ sz) = text $ "(_ BitVec " ++ show sz ++ ")"
smtType KUnbounded      = text   "Int"
smtType KReal           = text   "Real"
smtType KFloat          = text   "(_ FloatingPoint  8 24)"
smtType KDouble         = text   "(_ FloatingPoint 11 53)"
smtType (KUserSort s _) = text   s

cvtType :: SBVType -> Script
cvtType (SBVType []) = error "SBV.SMT.SMTLib2.cvtType: internal: received an empty type!"
cvtType (SBVType xs) = parens (hsep (map smtType body)) <+> smtType ret
  where (body, ret) = (init xs, last xs)

type SkolemMap = M.Map  SW [SW]
type TableMap  = IM.IntMap Script

cvtSW :: SkolemMap -> SW -> Script
cvtSW skolemMap s
  | Just ss <- s `M.lookup` skolemMap
  = parens (text (show s) <+> hsep (map (text . show) ss))
  | True
  = text (show s)

cvtCW :: RoundingMode -> CW -> Script
cvtCW rm cw = text $ cwToSMTLib rm cw

getTable :: TableMap -> Int -> Script
getTable m i
  | Just tn <- i `IM.lookup` m = tn
  | True                       = error $ "SBV.SMTLib2: Cannot locate table " ++ show i

cvtExp :: RoundingMode -> SkolemMap -> TableMap -> SBVExpr -> Script
cvtExp rm skolemMap tableMap expr@(SBVApp _ arguments) = sh expr
  where ssw      = cvtSW skolemMap
        bvOp     = all isBounded       arguments
        intOp    = any isInteger       arguments
        realOp   = any isReal          arguments
        doubleOp = any isDouble        arguments
        floatOp  = any isFloat         arguments
        boolOp   = all isBoolean       arguments

        bad | intOp = error $ msg "unbounded integers"
            | True  = error $ msg "real values"
            where msg k = "SBV.SMTLib2: Unsupported operation on " ++ k ++ ": " ++ show expr

        ensureBVOrBool = bvOp || boolOp || bad
        ensureBV       = bvOp || bad

        lift1  o _ [x]  = parens $ text o <+> x
        lift1  o _ sbvs = error $ "SBV.SMT.SMTLib2.sh.lift1: Unexpected arguments: "   ++ show (o, map render sbvs)

        lift1B bOp vOp
          | boolOp = lift1 bOp
          | True   = lift1 vOp

        lift2S oU oS sgn = lift2 (if sgn then oS else oU) sgn
        lift2Cmp o fo | doubleOp || floatOp = lift2 fo
                      | True                = lift2 o

        lift2B bOp vOp
          | boolOp = lift2 bOp
          | True   = lift2 vOp

        lift2  o _ [x, y] = parens $ text o <+> x <+> y
        lift2  o _ sbvs   = error $ "SBV.SMTLib2.sh.lift2: Unexpected arguments: "   ++ show (o, map render sbvs)

        addRM s = s ++ " " ++ smtRoundingMode rm

        -- lift a binary operation with rounding-mode added; used for floating-point arithmetic
        lift2WM o fo | doubleOp || floatOp = lift2 (addRM fo)
                     | True                = lift2 o
        lift1FP o fo | doubleOp || floatOp = lift1 fo
                     | True                = lift1 o

        liftAbs sgned args | doubleOp || floatOp = lift1 "fp.abs" sgned args
                           | intOp               = lift1 "abs"    sgned args
                           | bvOp, sgned         = mkAbs (head args) "bvslt" "bvneg"
                           | bvOp                = head args
                           | True                = mkAbs (head args) "<"     "-"
          where mkAbs x cmp neg = parens $ text "ite" <+> ltz <+> nx <+> x
                  where ltz = parens $ text cmp <+> x <+> z
                        nx  = parens $ text neg <+> x
                        z   = cvtCW rm (mkConstCW (kindOf (head arguments)) (0::Integer))

        eqBV  = lift2 "="
        neqBV = lift2 "distinct"

        equal sgn sbvs
          | doubleOp = lift2 "fp.eq" sgn sbvs
          | floatOp  = lift2 "fp.eq" sgn sbvs
          | True     = lift2 "="     sgn sbvs

        notEqual sgn sbvs
          | doubleOp || floatOp = parens $ text "not" <+> equal sgn sbvs
          | True                = lift2 "distinct" sgn sbvs

        unintComp o [a, b]
          | KUserSort s (Right _) <- kindOf (head arguments)
          = let idx v = parens $ text (s ++ "_constrIndex") <+> v
             in parens $ text o <+> idx a <+> idx b
        unintComp o sbvs = error $ "SBV.SMT.SMTLib2.sh.unintComp: Unexpected arguments: " ++ show (o, map render sbvs)

        sh (SBVApp Ite [a, b, c]) = parens $ text "ite" <+> ssw a <+> ssw b <+> ssw c

        sh (SBVApp (LkUp (t, aKnd, _, l) i e) [])
          | needsCheck = parens $ text "ite" <+> cond <+> ssw e <+> lkUp
          | True       = lkUp
          where needsCheck = case aKnd of
                              KBool         -> (2::Integer) > fromIntegral l
                              KBounded _ n  -> (2::Integer)^n > fromIntegral l
                              KUnbounded    -> True
                              KReal         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected real valued index"
                              KFloat        -> error "SBV.SMT.SMTLib2.cvtExp: unexpected float valued index"
                              KDouble       -> error "SBV.SMT.SMTLib2.cvtExp: unexpected double valued index"
                              KUserSort s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s
                lkUp = parens $ getTable tableMap t <+> ssw i
                cond
                 | hasSign i = parens $ text "or" <+> le0 <+> gtl
                 | True      = gtl
                (less, leq) = case aKnd of
                                KBool         -> error "SBV.SMT.SMTLib2.cvtExp: unexpected boolean valued index"
                                KBounded{}    -> if hasSign i then ("bvslt", "bvsle") else ("bvult", "bvule")
                                KUnbounded    -> ("<", "<=")
                                KReal         -> ("<", "<=")
                                KFloat        -> ("fp.lt", "fp.leq")
                                KDouble       -> ("fp.lt", "fp.geq")
                                KUserSort s _ -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s
                mkCnst = cvtCW rm . mkConstCW (kindOf i)
                le0  = parens $ text less <+> ssw i <+>  mkCnst 0
                gtl  = parens $ text leq  <+> mkCnst l <+> ssw i

        sh (SBVApp (IntCast f t) [a]) = handleIntCast f t (ssw a)

        sh (SBVApp (ArrEq i j) [])  = let ai = text $ "array_" ++ show i
                                          aj = text $ "array_" ++ show j
                                      in parens $ text "=" <+> ai <+> aj
        sh (SBVApp (ArrRead i) [a]) = parens $ text "select" <+> text ("array_" ++ show i) <+> ssw a

        sh (SBVApp (Uninterpreted nm) [])   = text nm
        sh (SBVApp (Uninterpreted nm) args) = parens $ text nm <+> hsep (map ssw args)

        sh (SBVApp (Extract i j) [a])
            | ensureBV = parens $ ext <+> ssw a
            where ext = parens $ text "_" <+> text "extract" <+> int i <+> int j

        sh (SBVApp (Rol i) [a])
           | bvOp  = rot ssw "rotate_left"  i a
           | intOp = sh (SBVApp (Shl i) [a])       -- Haskell treats rotateL as shiftL for unbounded values
           | True  = bad

        sh (SBVApp (Ror i) [a])
           | bvOp  = rot ssw "rotate_right" i a
           | intOp = sh (SBVApp (Shr i) [a])     -- Haskell treats rotateR as shiftR for unbounded values
           | True  = bad

        sh (SBVApp (Shl i) [a])
           | bvOp   = shft rm ssw "bvshl"  "bvshl"  i a
           | i < 0  = sh (SBVApp (Shr (-i)) [a])  -- flip sign/direction
           | intOp  = parens $ text "*" <+> ssw a <+> integer (bit i :: Integer) -- Implement shiftL by multiplication by 2^i
           | True   = bad

        sh (SBVApp (Shr i) [a])
           | bvOp  = shft rm ssw "bvlshr" "bvashr" i a
           | i < 0 = sh (SBVApp (Shl (-i)) [a])  -- flip sign/direction
           | intOp = parens $ text "div" <+> ssw a <+> integer (bit i :: Integer) -- Implement shiftR by division by 2^i
           | True  = bad

        sh (SBVApp op args)
          | Just f <- lookup op smtBVOpTable, ensureBVOrBool
          = f (any hasSign args) (map ssw args)
          where -- The first 4 operators below do make sense for Integer's in Haskell, but there's
                -- no obvious counterpart for them in the SMTLib translation.
                -- TODO: provide support for these.
                smtBVOpTable = [ (And,  lift2B "and" "bvand")
                               , (Or,   lift2B "or"  "bvor")
                               , (XOr,  lift2B "xor" "bvxor")
                               , (Not,  lift1B "not" "bvnot")
                               , (Join, lift2 "concat")
                               ]
        sh (SBVApp (Label _)                       [a]) = cvtSW skolemMap a  -- This won't be reached; but just in case!

        sh (SBVApp (IEEEFP (FP_Cast kFrom kTo m)) args) = handleFPCast kFrom kTo (ssw m) (hsep (map ssw args))
        sh (SBVApp (IEEEFP w                    ) args) = parens $ text (show w) <+> hsep (map ssw args)

        sh inp@(SBVApp op args)
          | intOp, Just f <- lookup op smtOpIntTable
          = f True dargs
          | boolOp, Just f <- lookup op boolComps
          = f dargs
          | bvOp, Just f <- lookup op smtOpBVTable
          = f (any hasSign args) dargs
          | realOp, Just f <- lookup op smtOpRealTable
          = f (any hasSign args) dargs
          | floatOp || doubleOp, Just f <- lookup op smtOpFloatDoubleTable
          = f (any hasSign args) dargs
          | Just f <- lookup op uninterpretedTable
          = f dargs
          | True
          = error $ "SBV.SMT.SMTLib2.cvtExp.sh: impossible happened; can't translate: " ++ show inp
          where dargs = map ssw args

                smtOpBVTable  = [ (Plus,          lift2   "bvadd")
                                , (Minus,         lift2   "bvsub")
                                , (Times,         lift2   "bvmul")
                                , (UNeg,          lift1B  "not"    "bvneg")
                                , (Abs,           liftAbs)
                                , (Quot,          lift2S  "bvudiv" "bvsdiv")
                                , (Rem,           lift2S  "bvurem" "bvsrem")
                                , (Equal,         eqBV)
                                , (NotEqual,      neqBV)
                                , (LessThan,      lift2S  "bvult" "bvslt")
                                , (GreaterThan,   lift2S  "bvugt" "bvsgt")
                                , (LessEq,        lift2S  "bvule" "bvsle")
                                , (GreaterEq,     lift2S  "bvuge" "bvsge")
                                ]

                -- Boolean comparisons.. SMTLib's bool type doesn't do comparisons, but Haskell does.. Sigh
                boolComps      = [ (LessThan,      blt)
                                 , (GreaterThan,   blt . swp)
                                 , (LessEq,        blq)
                                 , (GreaterEq,     blq . swp)
                                 ]
                               where blt [x, y] = parens $ text "and" <+> parens (text "not" <+> x) <+> y
                                     blt xs     = error $ "SBV.SMT.SMTLib2.boolComps.blt: Impossible happened, incorrect arity (expected 2): " ++ show (map render xs)
                                     blq [x, y] = parens $ text "or" <+> parens (text "not" <+> x) <+> y
                                     blq xs     = error $ "SBV.SMT.SMTLib2.boolComps.blq: Impossible happened, incorrect arity (expected 2): " ++ show (map render xs)
                                     swp [x, y] = [y, x]
                                     swp xs     = error $ "SBV.SMT.SMTLib2.boolComps.swp: Impossible happened, incorrect arity (expected 2): " ++ show (map render xs)

                smtOpRealTable =  smtIntRealShared
                               ++ [ (Quot,        lift2WM "/" "fp.div")
                                  ]

                smtOpIntTable  = smtIntRealShared
                               ++ [ (Quot,        lift2   "div")
                                  , (Rem,         lift2   "mod")
                                  ]

                smtOpFloatDoubleTable =  smtIntRealShared
                                      ++ [(Quot, lift2WM "/" "fp.div")]

                smtIntRealShared  = [ (Plus,          lift2WM "+" "fp.add")
                                    , (Minus,         lift2WM "-" "fp.sub")
                                    , (Times,         lift2WM "*" "fp.mul")
                                    , (UNeg,          lift1FP "-" "fp.neg")
                                    , (Abs,           liftAbs)
                                    , (Equal,         equal)
                                    , (NotEqual,      notEqual)
                                    , (LessThan,      lift2Cmp  "<"  "fp.lt")
                                    , (GreaterThan,   lift2Cmp  ">"  "fp.gt")
                                    , (LessEq,        lift2Cmp  "<=" "fp.leq")
                                    , (GreaterEq,     lift2Cmp  ">=" "fp.geq")
                                    ]
                -- equality and comparisons are the only thing that works on uninterpreted sorts
                uninterpretedTable = [ (Equal,       lift2S "="        "="        True)
                                     , (NotEqual,    lift2S "distinct" "distinct" True)
                                     , (LessThan,    unintComp "<")
                                     , (GreaterThan, unintComp ">")
                                     , (LessEq,      unintComp "<=")
                                     , (GreaterEq,   unintComp ">=")
                                     ]

-----------------------------------------------------------------------------------------------
-- Casts supported by SMTLib. (From: <http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml>)
--   ; from another floating point sort
--   ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb) (_ FloatingPoint eb sb))
--
--   ; from real
--   ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
--
--   ; from signed machine integer, represented as a 2's complement bit vector
--   ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
--
--   ; from unsigned machine integer, represented as bit vector
--   ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
--
--   ; to unsigned machine integer, represented as a bit vector
--   ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))
--
--   ; to signed machine integer, represented as a 2's complement bit vector
--   ((_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m)) 
--
--   ; to real
--   (fp.to_real (_ FloatingPoint eb sb) Real)
-----------------------------------------------------------------------------------------------

handleFPCast :: Kind -> Kind -> Script -> Script -> Script
handleFPCast kFrom kTo rm input
  | kFrom == kTo
  = input
  | True
  = parens $ cast kFrom kTo input
  where addRM a s = s <+> rm <+> a

        absRM a s = text "ite" <+> parens (text "fp.isNegative" <+> a) <+> parens cvt1 <+> parens cvt2
          where cvt1 = text "bvneg" <+> parens (s <+> rm <+> parens (text "fp.abs" <+> a))
                cvt2 =                          s <+> rm <+> a

        -- To go and back from Ints, we detour through reals
        cast KUnbounded         KFloat             a = text "(_ to_fp 8 24)"  <+> rm <+> parens (text "to_real" <+> a)
        cast KUnbounded         KDouble            a = text "(_ to_fp 11 53)" <+> rm <+> parens (text "to_real" <+> a)
        cast KFloat             KUnbounded         a = text "to_int" <+> parens (text "fp.to_real" <+> a)
        cast KDouble            KUnbounded         a = text "to_int" <+> parens (text "fp.to_real" <+> a)

        -- To float/double
        cast (KBounded False _) KFloat             a = addRM a $ text "(_ to_fp_unsigned 8 24)"
        cast (KBounded False _) KDouble            a = addRM a $ text "(_ to_fp_unsigned 11 53)"
        cast (KBounded True  _) KFloat             a = addRM a $ text "(_ to_fp 8 24)"
        cast (KBounded True  _) KDouble            a = addRM a $ text "(_ to_fp 11 53)"
        cast KReal              KFloat             a = addRM a $ text "(_ to_fp 8 24)"
        cast KReal              KDouble            a = addRM a $ text "(_ to_fp 11 53)"

        -- Between floats
        cast KFloat             KFloat             a = addRM a $ text "(_ to_fp 8 24)"
        cast KFloat             KDouble            a = addRM a $ text "(_ to_fp 11 53)"
        cast KDouble            KFloat             a = addRM a $ text "(_ to_fp 8 24)"
        cast KDouble            KDouble            a = addRM a $ text "(_ to_fp 11 53)"

        -- From float/double
        cast KFloat             (KBounded False m) a = absRM a $ parens $ text "_ fp.to_ubv" <+> int m
        cast KDouble            (KBounded False m) a = absRM a $ parens $ text "_ fp.to_ubv" <+> int m
        cast KFloat             (KBounded True  m) a = addRM a $ parens $ text "_ fp.to_sbv" <+> int m
        cast KDouble            (KBounded True  m) a = addRM a $ parens $ text "_ fp.to_sbv" <+> int m
        cast KFloat             KReal              a = text "fp.to_real" <+> a
        cast KDouble            KReal              a = text "fp.to_real" <+> a

        -- Nothing else should come up:
        cast f                  d                  _ = error $ "SBV.SMTLib2: Unexpected FPCast from: " ++ show f ++ " to " ++ show d

rot :: (SW -> Script) -> String -> Int -> SW -> Script
rot ssw o c x = parens $ parens (text o <+> int c) <+> ssw x

shft :: RoundingMode -> (SW -> Script) -> String -> String -> Int -> SW -> Script
shft rm ssw oW oS c x = parens $ text o <+> ssw x <+> cvtCW rm c'
   where s  = hasSign x
         c' = mkConstCW (kindOf x) c
         o  = if s then oS else oW

-- Various integer casts
handleIntCast :: Kind -> Kind -> Script -> Script
handleIntCast kFrom kTo a
  | kFrom == kTo
  = a
  | True
  = case kFrom of
      KBounded s m -> case kTo of
                        KBounded _ n -> fromBV (if s then signExtend else zeroExtend) m n
                        KUnbounded   -> b2i s m
                        _            -> noCast

      KUnbounded   -> case kTo of
                        KReal        -> parens $ text "to_real" <+> a
                        KBounded _ n -> i2b n
                        _            -> noCast

      _            -> noCast

  where noCast  = error $ "SBV.SMTLib2: Unexpected integer cast from: " ++ show kFrom ++ " to " ++ show kTo

        fromBV upConv m n
         | n > m  = upConv  (n - m)
         | m == n = a
         | True   = extract (n - 1)

        i2b n = parens $ text "let" <+> parens reduced <+> parens (text "let" <+> defs <+> text body)
          where b i      = show (bit i :: Integer)
                reduced  = parens $ text "__a" <+> parens (text "mod" <+> a <+> text (b n))
                mkBit 0  = text "(__a0 (ite (= (mod __a 2) 0) #b0 #b1))"
                mkBit i  = text $ "(__a" ++ show i ++ " (ite (= (mod (div __a " ++ b i ++ ") 2) 0) #b0 #b1))"
                defs     = hsep (map mkBit [0 .. n - 1])
                body     = foldr1 (\c r -> "(concat " ++ c ++ " " ++ r ++ ")") ["__a" ++ show i | i <- [n-1, n-2 .. 0]]

        b2i s m
          | s    = parens $ text "-" <+> val <+> valIf (2^m) sign
          | True = val
          where valIf v b = parens $ text "ite" <+> (parens (text "=" <+> b <+> text "#b1") <+> integer v <+> text "0")
                getBit i  = parens $ parens (text "_ extract" <+> int i <+> int i) <+> a
                bitVal i  = valIf (2^i) (getBit i)
                val       = parens $ text "+" <+> hsep (map bitVal [0 .. m-1])
                sign      = getBit (m-1)

        signExtend i = parens $ parens (text "_ sign_extend" <+> int i)              <+> a
        zeroExtend i = parens $ parens (text "_ zero_extend" <+> int i)              <+> a
        extract    i = parens $ parens (text "_ extract"     <+> int i <+> text "0") <+> a
