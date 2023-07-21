module Language.Granule.Benchmarks where

rootDir :: String
rootDir = "frontend/tests/cases/synthesis/"

benchmarkList :: [(String, String, String, Bool)]
benchmarkList = [
    -- -- Comp
    -- ("0/1",                                 "Comp", "comp/01.gr",               False),
    -- ("CBN",                                 "Comp", "comp/cbn.gr",              False),
    -- ("CBV",                                 "Comp", "comp/cbv.gr",              False),
    -- ("$\\circ\\textit{coK}_\\mathbb{N}$",   "Comp", "comp/con.gr",              False),
    -- ("$\\circ\\textit{coK}_\\mathcal{R}$",  "Comp", "comp/cok.gr",              False),
    -- ("Mult",                                "Comp", "comp/mult.gr",             False),

    -- -- Hilbert
    -- ("SKI",                  "Hilbert", "hilbert/ski.gr",                       False),
    -- ("$\\otimes$-Intro",     "Hilbert", "hilbert/andIntro.gr",                  False),
    -- ("$\\otimes$-Elim",      "Hilbert", "hilbert/andElim.gr",                   False),
    -- ("$\\oplus$-Intro",      "Hilbert", "hilbert/orIntro.gr",                   False),
    -- ("$\\oplus$-Elim",       "Hilbert", "hilbert/orElim.gr",                    False),

    -- -- Dist 
    -- ("$\\multimap$-!",               "Dist", "dist/funBang.gr",                 False),
    -- ("$\\multimap$-$\\mathbb{N}$",   "Dist", "dist/funN.gr",                    False),
    -- ("$\\multimap$-$\\mathbb{R}$",   "Dist", "dist/funR.gr",                    False),
    -- ("$\\oplus$-!",                  "Dist", "dist/sumBang.gr",                 False),
    -- ("$\\oplus$-$\\mathbb{N}$",      "Dist", "dist/sumN.gr",                    False),
    -- ("$\\oplus$-$\\mathcal{R}$",     "Dist", "dist/sumR.gr",                    False),
    -- ("$\\otimes$-!",                 "Dist", "dist/prodBang.gr",                False),
    -- ("$\\otimes$-$\\mathbb{N}$",     "Dist", "dist/prodN.gr",                   False),
    -- ("$\\otimes$-$\\mathcal{R}$",    "Dist", "dist/prodR.gr",                   False),

    -- -- Vec 
    -- ("vec5",     "Vec", "vec/vec5.gr",                                          False),
    -- ("vec10",    "Vec", "vec/vec10.gr",                                         False),
    -- ("vec15",    "Vec", "vec/vec15.gr",                                         False),
    -- ("vec20",    "Vec", "vec/vec20.gr",                                         False),

    -- -- Misc
    -- ("copy",                "Misc", "misc/copy.gr",                             False),
    -- ("share",               "Misc", "misc/share.gr",                            False),
    -- ("split-$\\oplus$",     "Misc", "misc/shareSum.gr",                         False),
    -- ("split-$\\otimes$",    "Misc", "misc/shareProd.gr",                        False),

    -- -- *** GRADED BASE *** --

    -- -- List
    ("append",                 "List", "graded-base/list/append.gr",            True),
    ("concat",                 "List", "graded-base/list/concat.gr",            True),
    ("empty",                  "List", "graded-base/list/nil.gr",               True),
    ("snoc",                   "List", "graded-base/list/snoc.gr",              True),
    ("drop",                   "List", "graded-base/list/drop.gr",              True),
    ("flatten",                "List", "graded-base/list/flatten.gr",           True),
    ("bind",                   "List", "graded-base/list/bind.gr",              True),
    ("return",                 "List", "graded-base/list/return.gr",            True),
    ("inc",                    "List", "graded-base/list/inc.gr",               True),
    ("head",                   "List", "graded-base/list/head.gr",              True),
    ("tail",                   "List", "graded-base/list/tail.gr",              True),
    ("last",                   "List", "graded-base/list/last.gr",              True),
    ("length",                 "List", "graded-base/list/length.gr",            True),
    ("map",                    "List", "graded-base/list/map.gr",               True),
    ("replicate5",             "List", "graded-base/list/replicate5.gr",        True),
    ("replicate10",            "List", "graded-base/list/replicate10.gr",       True),
    ("replicateN",             "List", "graded-base/list/replicateN.gr",        True),
    ("stutter",                "List", "graded-base/list/stutter.gr",           True),
    ("sum",                    "List", "graded-base/list/sum.gr",               True),

--     -- Stream 
    ("build",                  "Stream", "graded-base/stream/build.gr",         True),
    ("map",                    "Stream", "graded-base/stream/map.gr",           True),
    ("take1",                  "Stream", "graded-base/stream/take1.gr",         True),
    ("take2",                  "Stream", "graded-base/stream/take2.gr",         True),
    ("take3",                  "Stream", "graded-base/stream/take3.gr",         True),

    -- -- Bool 
    ("neg",                    "Bool", "graded-base/bool/neg.gr",               True),
    ("and",                    "Bool", "graded-base/bool/and.gr",               True),
    ("impl",                   "Bool", "graded-base/bool/impl.gr",              True),
    ("or",                     "Bool", "graded-base/bool/or.gr",                True),
    ("xor",                    "Bool", "graded-base/bool/xor.gr",               True),
    ("copy",                   "Bool", "graded-base/bool/boolCopy.gr",          False),
    ("toBoolPair",             "Bool", "graded-base/bool/toBoolPair.gr",        False),
    ("toBoolPair2",            "Bool", "graded-base/bool/toBoolPair2.gr",       False),

    -- Maybe
    ("bind",                    "Maybe", "graded-base/maybe/bind.gr",           True),
    ("fromMaybe",               "Maybe", "graded-base/maybe/fromMaybe.gr",      True),
    ("return",                  "Maybe", "graded-base/maybe/toJust.gr",         True),
    ("isJust",                  "Maybe", "graded-base/maybe/isJust.gr",         True),
    ("isNothing",               "Maybe", "graded-base/maybe/isNothing.gr",      True),
    ("map",                     "Maybe", "graded-base/maybe/map.gr",            True),
    ("maybePair",               "Maybe", "graded-base/maybe/maybePair.gr",      False),
    ("mplus",                   "Maybe", "graded-base/maybe/mplus.gr",          True),
    ("safeHead",                "Maybe", "graded-base/maybe/safeHead.gr",       False),

--     -- Nat 
    ("isEven",                  "Nat", "graded-base/nat/isEven.gr",             True),
    ("pred",                    "Nat", "graded-base/nat/pred.gr",               True),
    ("succ",                    "Nat", "graded-base/nat/succ.gr",               True),
    ("sum",                     "Nat", "graded-base/nat/sum.gr",                True),

--     -- Tree 
    ("map",                     "Tree", "graded-base/tree/map.gr",              True),
    ("stutter",                 "Tree", "graded-base/tree/stutter.gr",          True),
    ("sum",                     "Tree", "graded-base/tree/sum.gr",              True),

    -- Misc
    ("compose",                 "Misc", "graded-base/misc/compose.gr",          True),
    ("copy",                    "Misc", "graded-base/misc/copy.gr",             True),
    ("push",                    "Misc", "graded-base/misc/push-fun-gen.gr",     True)
--     ("SKI",                     "Misc", "graded-base/misc/SKI.gr",              False)

                ]



benchmarkListFullPath :: [(String, String, String, Bool)] -> [(String, String, String, Bool)]
benchmarkListFullPath = map (\(title, cat, path, incl) -> (title, cat, rootDir <> path, incl))

benchmarksToRun :: [(String, String, String, Bool)] -> [(String, String, String, Bool)]
benchmarksToRun = benchmarkListFullPath . filter (\(_,_,_,b) -> b) 

benchmarksByCategory :: [String] -> Bool -> [(String, String, String, Bool)]
benchmarksByCategory bs onlyIncls = foldr
      (\ c
         -> (++)
              (filter
                 (\ (_, c', _, incl) -> c' == c && (incl || not onlyIncls))
                 (benchmarkListFullPath benchmarkList)))
      []
      bs 

categorySize :: String -> Bool -> Int
categorySize cat onlyIncls = length $ benchmarksByCategory [cat] onlyIncls





