module Language.Granule.Benchmarks where

rootDir :: String
rootDir = "frontend/tests/cases/synthesis/"

benchmarkList :: [(String, String, String)]
benchmarkList = [
    -- Comp
    ("0/1",                                 "Comp", "comp/01.gr"),
    ("CBN",                                 "Comp", "comp/cbn.gr"),
    ("CBV",                                 "Comp", "comp/cbv.gr"),
    ("$\\circ\\textit{coK}_\\mathbb{N}$",   "Comp", "comp/con.gr"), 
    ("$\\circ\\textit{coK}_\\mathcal{R}$",  "Comp", "comp/cok.gr"), 
    ("Mult",                                "Comp", "comp/mult.gr"),

    -- Hilbert
    ("SKI",                  "Hilbert", "hilbert/ski.gr"),
    ("$\\otimes$-Intro",     "Hilbert", "hilbert/andIntro.gr"),
    ("$\\otimes$-Elim",      "Hilbert", "hilbert/andElim.gr"),
    ("$\\oplus$-Intro",      "Hilbert", "hilbert/orIntro.gr"),
    ("$\\oplus$-Elim",       "Hilbert", "hilbert/orElim.gr"),

    -- Dist 
    ("$\\multimap$-!",               "Dist", "dist/funBang.gr"),
    ("$\\multimap$-$\\mathbb{N}$",   "Dist", "dist/funN.gr"),
    ("$\\multimap$-$\\mathbb{R}$",   "Dist", "dist/funR.gr"),
    ("$\\oplus$-!",                  "Dist", "dist/sumBang.gr"),
    ("$\\oplus$-$\\mathbb{N}$",      "Dist", "dist/sumN.gr"),
    ("$\\oplus$-$\\mathcal{R}$",     "Dist", "dist/sumR.gr"),
    ("$\\otimes$-!",                 "Dist", "dist/prodBang.gr"),
    ("$\\otimes$-$\\mathbb{N}$",     "Dist", "dist/prodN.gr"),
    ("$\\otimes$-$\\mathcal{R}$",    "Dist", "dist/prodR.gr"),

    -- Vec 
    ("vec5",     "Vec", "vec/vec5.gr"),
    ("vec10",    "Vec", "vec/vec10.gr"),
    ("vec15",    "Vec", "vec/vec15.gr"),
    ("vec20",    "Vec", "vec/vec20.gr"),

    -- Misc
    ("Copy",                "Misc", "misc/copy.gr"),
    ("share",               "Misc", "misc/share.gr"),
    ("split-$\\oplus$",     "Misc", "misc/shareSum.gr"),
    ("split-$\\otimes$",    "Misc", "misc/shareProd.gr"),

    ("Test1",              "Tests", "test/test1.gr"),
    ("Test2",              "Tests2", "test/test2.gr"),

    -- *** GRADED BASE *** --
    ("list_append",                     "List", "graded-base/lists/list1.gr"),
    ("list_map",                        "List", "graded-base/lists/list2.gr"),
    ("list_concat",                     "List", "graded-base/lists/list3.gr"),
    ("list_drop",                       "List", "graded-base/lists/list4.gr"),
    ("list_even_parity",                "List", "graded-base/lists/list5.gr"),
    ("list_fold",                       "List", "graded-base/lists/list6.gr"),
    ("list_hd",                         "List", "graded-base/lists/list7.gr")

                ]


sPointBenchmarkList :: [(String, String, String)]
sPointBenchmarkList = [
    ("list_append",                     "List", "graded-base/spoint/lists/list1.gr"),
    ("list_map",                        "List", "graded-base/spoint/lists/list2.gr"),
    ("list_concat",                     "List", "graded-base/spoint/lists/list3.gr"),
    ("list_drop",                       "List", "graded-base/spoint/lists/list4.gr"),
    ("list_even_parity",                "List", "graded-base/spoint/lists/list5.gr"),
    ("list_fold",                       "List", "graded-base/spoint/lists/list6.gr"),
    ("list_hd",                         "List", "graded-base/spoint/lists/list7.gr")
            ]

benchmarkListFullPath :: [(String, String, String)] -> [(String, String, String)]
benchmarkListFullPath bl = map (\(title, cat, path) -> (title, cat, rootDir <> path)) bl

benchmarksByCategory :: [String] -> [(String, String, String)]
benchmarksByCategory [] = []
benchmarksByCategory (c:cats) = filter (\(_, c', _) -> c' == c) (benchmarkListFullPath benchmarkList) ++ benchmarksByCategory cats

sPointBenchmarksByCategory :: [String] -> [(String, String, String)]
sPointBenchmarksByCategory [] = []
sPointBenchmarksByCategory (c:cats) = filter (\(_, c', _) -> c' == c) (benchmarkListFullPath sPointBenchmarkList) ++ sPointBenchmarksByCategory cats



