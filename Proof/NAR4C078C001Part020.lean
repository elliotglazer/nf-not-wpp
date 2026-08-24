import NAR4C078C001Part019

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb078_fresh_1359 (g : Var) : (nb078_alpha_dummy_680 g) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv) := by
  simpa only [nb078_alpha_dummy_680] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_673 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_674 g)))).fv) 0

theorem nb078_fresh_1360 : (nb078_alpha_dummy_715) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv) := by
  simpa only [nb078_alpha_dummy_715] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_706)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_707)))).fv) 0

theorem nb078_fresh_1361 (g : Var) : (nb078_alpha_dummy_716 g) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv) := by
  simpa only [nb078_alpha_dummy_716] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_709 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_710 g)))).fv) 0

theorem nb078_fresh_1362 : (nb078_alpha_dummy_751) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv) := by
  simpa only [nb078_alpha_dummy_751] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_742)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_743)))).fv) 0

theorem nb078_fresh_1363 (g : Var) : (nb078_alpha_dummy_752 g) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv) := by
  simpa only [nb078_alpha_dummy_752] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_745 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_746 g)))).fv) 0

theorem nb078_fresh_1364 : (nb078_alpha_dummy_799) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv) := by
  simpa only [nb078_alpha_dummy_799] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_790)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_791)))).fv) 0

theorem nb078_fresh_1365 (h : Var) : (nb078_alpha_dummy_800 h) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv) := by
  simpa only [nb078_alpha_dummy_800] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_793 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_794 h)))).fv) 0

theorem nb078_fresh_1366 : (nb078_alpha_dummy_835) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv) := by
  simpa only [nb078_alpha_dummy_835] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_826)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_827)))).fv) 0

theorem nb078_fresh_1367 (h : Var) : (nb078_alpha_dummy_836 h) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv) := by
  simpa only [nb078_alpha_dummy_836] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_829 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_830 h)))).fv) 0

theorem nb078_fresh_1368 : (nb078_alpha_dummy_877) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv) := by
  simpa only [nb078_alpha_dummy_877] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv) 0

theorem nb078_fresh_1369 (h : Var) : (nb078_alpha_dummy_878 h) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv) := by
  simpa only [nb078_alpha_dummy_878] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv) 0

theorem nb078_fresh_1370 : (nb078_alpha_dummy_913) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv) := by
  simpa only [nb078_alpha_dummy_913] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv) 0

theorem nb078_fresh_1371 (h : Var) : (nb078_alpha_dummy_914 h) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv) := by
  simpa only [nb078_alpha_dummy_914] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv) 0

theorem nb078_fresh_1372 : (nb078_alpha_dummy_949) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv) := by
  simpa only [nb078_alpha_dummy_949] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv) 0

theorem nb078_fresh_1373 (h : Var) : (nb078_alpha_dummy_950 h) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv) := by
  simpa only [nb078_alpha_dummy_950] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv) 0

theorem nb078_fresh_1374 : (nb078_alpha_dummy_989) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv) := by
  simpa only [nb078_alpha_dummy_989] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv) 0

theorem nb078_fresh_1375 (h : Var) : (nb078_alpha_dummy_990 h) ∉ (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv) := by
  simpa only [nb078_alpha_dummy_990] using freshVar_not_mem (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv) 0

theorem nb078_fresh_1376 : (nb078_alpha_dummy_049) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_049] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1377 (f : Var) : (nb078_alpha_dummy_050 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_050] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1378 : (nb078_alpha_dummy_085) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_085] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1379 (f : Var) : (nb078_alpha_dummy_086 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_086] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1380 : (nb078_alpha_dummy_127) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_096))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_127] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_096))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1381 (f : Var) : (nb078_alpha_dummy_128 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_128] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1382 : (nb078_alpha_dummy_1041) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1041] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1383 (h : Var) : (nb078_alpha_dummy_1042 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1042] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1384 : (nb078_alpha_dummy_1089) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1089] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1385 (h : Var) : (nb078_alpha_dummy_1090 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1090] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1386 : (nb078_alpha_dummy_1125) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1125] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1387 (h : Var) : (nb078_alpha_dummy_1126 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1126] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1388 : (nb078_alpha_dummy_1167) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1167] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1389 (h : Var) : (nb078_alpha_dummy_1168 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1168] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1390 : (nb078_alpha_dummy_1203) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1203] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1391 (h : Var) : (nb078_alpha_dummy_1204 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1204] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1392 : (nb078_alpha_dummy_1239) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1239] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1393 (h : Var) : (nb078_alpha_dummy_1240 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_1240] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1394 : (nb078_alpha_dummy_163) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_132))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_163] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_132))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1395 (f : Var) : (nb078_alpha_dummy_164 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_164] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1396 : (nb078_alpha_dummy_199) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_199] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1397 (f : Var) : (nb078_alpha_dummy_200 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_200] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1398 : (nb078_alpha_dummy_239) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_208))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_239] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_208))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1399 (f : Var) : (nb078_alpha_dummy_240 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_240] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1400 : (nb078_alpha_dummy_279) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_248))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_279] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_248))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1401 (f : Var) : (nb078_alpha_dummy_280 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_280] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1402 : (nb078_alpha_dummy_327) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_296))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_327] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_296))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1403 (g : Var) : (nb078_alpha_dummy_328 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_328] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1404 : (nb078_alpha_dummy_363) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_363] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_332))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1405 (g : Var) : (nb078_alpha_dummy_364 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_364] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1406 : (nb078_alpha_dummy_405) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_374))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_405] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_374))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1407 (g : Var) : (nb078_alpha_dummy_406 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_406] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1408 : (nb078_alpha_dummy_441) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_410))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_441] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_410))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1409 (g : Var) : (nb078_alpha_dummy_442 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_442] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1410 : (nb078_alpha_dummy_477) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_477] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1411 (g : Var) : (nb078_alpha_dummy_478 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_478] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1412 : (nb078_alpha_dummy_517) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_486))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_517] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_486))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1413 (g : Var) : (nb078_alpha_dummy_518 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_518] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1414 : (nb078_alpha_dummy_561) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_530))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_561] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_530))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1415 (g : Var) : (nb078_alpha_dummy_562 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_562] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1416 : (nb078_alpha_dummy_609) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_578))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_609] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_578))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1417 (g : Var) : (nb078_alpha_dummy_610 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_610] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1418 : (nb078_alpha_dummy_645) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_645] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1419 (g : Var) : (nb078_alpha_dummy_646 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_646] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1420 : (nb078_alpha_dummy_687) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_656))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_687] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_656))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1421 (g : Var) : (nb078_alpha_dummy_688 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_688] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1422 : (nb078_alpha_dummy_723) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_692))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_723] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_692))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1423 (g : Var) : (nb078_alpha_dummy_724 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_724] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1424 : (nb078_alpha_dummy_759) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_728))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_759] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_728))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1425 (g : Var) : (nb078_alpha_dummy_760 g) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_760] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1426 : (nb078_alpha_dummy_807) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_776))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_807] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_776))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1427 (h : Var) : (nb078_alpha_dummy_808 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_808] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1428 : (nb078_alpha_dummy_843) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_843] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1429 (h : Var) : (nb078_alpha_dummy_844 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_844] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1430 : (nb078_alpha_dummy_885) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_854))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_885] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_854))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1431 (h : Var) : (nb078_alpha_dummy_886 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_886] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1432 : (nb078_alpha_dummy_921) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_890))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_921] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_890))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1433 (h : Var) : (nb078_alpha_dummy_922 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_922] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1434 : (nb078_alpha_dummy_957) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_957] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1435 (h : Var) : (nb078_alpha_dummy_958 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_958] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1436 : (nb078_alpha_dummy_997) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_966))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_997] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_966))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1437 (h : Var) : (nb078_alpha_dummy_998 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb078_alpha_dummy_998] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb078_fresh_1438 : (nb078_alpha_dummy_037) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv) := by
  simpa only [nb078_alpha_dummy_037] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv) 0

theorem nb078_fresh_1439 (f : Var) : (nb078_alpha_dummy_038 f) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv) := by
  simpa only [nb078_alpha_dummy_038] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv) 0

theorem nb078_fresh_1440 : (nb078_alpha_dummy_073) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv) := by
  simpa only [nb078_alpha_dummy_073] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv) 0

theorem nb078_fresh_1441 (f : Var) : (nb078_alpha_dummy_074 f) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv) := by
  simpa only [nb078_alpha_dummy_074] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f)) (Class.cv (nb078_alpha_dummy_072 f)))).fv) 0

theorem nb078_fresh_1442 : (nb078_alpha_dummy_1029) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv) := by
  simpa only [nb078_alpha_dummy_1029] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv) 0

theorem nb078_fresh_1443 (h : Var) : (nb078_alpha_dummy_1030 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1030] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv) 0

theorem nb078_fresh_1444 : (nb078_alpha_dummy_1077) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv) := by
  simpa only [nb078_alpha_dummy_1077] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv) 0

theorem nb078_fresh_1445 (h : Var) : (nb078_alpha_dummy_1078 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1078] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h)) (Class.cv (nb078_alpha_dummy_1076 h)))).fv) 0

theorem nb078_fresh_1446 : (nb078_alpha_dummy_115) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv) := by
  simpa only [nb078_alpha_dummy_115] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv) 0

theorem nb078_fresh_1447 : (nb078_alpha_dummy_1113) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv) := by
  simpa only [nb078_alpha_dummy_1113] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv) 0

theorem nb078_fresh_1448 (h : Var) : (nb078_alpha_dummy_1114 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1114] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h)) (Class.cv (nb078_alpha_dummy_1112 h)))).fv) 0

theorem nb078_fresh_1449 (f : Var) : (nb078_alpha_dummy_116 f) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv) := by
  simpa only [nb078_alpha_dummy_116] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f)) (Class.cv (nb078_alpha_dummy_114 f)))).fv) 0

theorem nb078_fresh_1450 : (nb078_alpha_dummy_1155) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv) := by
  simpa only [nb078_alpha_dummy_1155] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv) 0

theorem nb078_fresh_1451 (h : Var) : (nb078_alpha_dummy_1156 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h)) (Class.cv (nb078_alpha_dummy_1154 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h)) (Class.cv (nb078_alpha_dummy_1154 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1156] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h)) (Class.cv (nb078_alpha_dummy_1154 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h)) (Class.cv (nb078_alpha_dummy_1154 h)))).fv) 0

theorem nb078_fresh_1452 : (nb078_alpha_dummy_1191) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv) := by
  simpa only [nb078_alpha_dummy_1191] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv) 0

theorem nb078_fresh_1453 (h : Var) : (nb078_alpha_dummy_1192 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h)) (Class.cv (nb078_alpha_dummy_1190 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h)) (Class.cv (nb078_alpha_dummy_1190 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1192] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h)) (Class.cv (nb078_alpha_dummy_1190 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h)) (Class.cv (nb078_alpha_dummy_1190 h)))).fv) 0

theorem nb078_fresh_1454 : (nb078_alpha_dummy_1227) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv) := by
  simpa only [nb078_alpha_dummy_1227] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv) 0

theorem nb078_fresh_1455 (h : Var) : (nb078_alpha_dummy_1228 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h)) (Class.cv (nb078_alpha_dummy_1226 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h)) (Class.cv (nb078_alpha_dummy_1226 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1228] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h)) (Class.cv (nb078_alpha_dummy_1226 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h)) (Class.cv (nb078_alpha_dummy_1226 h)))).fv) 0

theorem nb078_fresh_1456 : (nb078_alpha_dummy_151) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv) := by
  simpa only [nb078_alpha_dummy_151] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv) 0

theorem nb078_fresh_1457 (f : Var) : (nb078_alpha_dummy_152 f) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv) := by
  simpa only [nb078_alpha_dummy_152] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f)) (Class.cv (nb078_alpha_dummy_150 f)))).fv) 0

theorem nb078_fresh_1458 : (nb078_alpha_dummy_187) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv) := by
  simpa only [nb078_alpha_dummy_187] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv) 0

theorem nb078_fresh_1459 (f : Var) : (nb078_alpha_dummy_188 f) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv) := by
  simpa only [nb078_alpha_dummy_188] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv) 0

theorem nb078_fresh_1460 : (nb078_alpha_dummy_227) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv) := by
  simpa only [nb078_alpha_dummy_227] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv) 0

theorem nb078_fresh_1461 (f : Var) : (nb078_alpha_dummy_228 f) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv) := by
  simpa only [nb078_alpha_dummy_228] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv) 0

theorem nb078_fresh_1462 : (nb078_alpha_dummy_267) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv) := by
  simpa only [nb078_alpha_dummy_267] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv) 0

theorem nb078_fresh_1463 (f : Var) : (nb078_alpha_dummy_268 f) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv) := by
  simpa only [nb078_alpha_dummy_268] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv) 0

theorem nb078_fresh_1464 : (nb078_alpha_dummy_315) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv) := by
  simpa only [nb078_alpha_dummy_315] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv) 0

theorem nb078_fresh_1465 (g : Var) : (nb078_alpha_dummy_316 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv) := by
  simpa only [nb078_alpha_dummy_316] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv) 0

theorem nb078_fresh_1466 : (nb078_alpha_dummy_351) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv) := by
  simpa only [nb078_alpha_dummy_351] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_346)) (Class.cv (nb078_alpha_dummy_347)))).fv) 0

theorem nb078_fresh_1467 (g : Var) : (nb078_alpha_dummy_352 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv) := by
  simpa only [nb078_alpha_dummy_352] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_349 g)) (Class.cv (nb078_alpha_dummy_350 g)))).fv) 0

theorem nb078_fresh_1468 : (nb078_alpha_dummy_393) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv) := by
  simpa only [nb078_alpha_dummy_393] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_388)) (Class.cv (nb078_alpha_dummy_389)))).fv) 0

theorem nb078_fresh_1469 (g : Var) : (nb078_alpha_dummy_394 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv) := by
  simpa only [nb078_alpha_dummy_394] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_391 g)) (Class.cv (nb078_alpha_dummy_392 g)))).fv) 0

theorem nb078_fresh_1470 : (nb078_alpha_dummy_429) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv) := by
  simpa only [nb078_alpha_dummy_429] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_424)) (Class.cv (nb078_alpha_dummy_425)))).fv) 0

theorem nb078_fresh_1471 (g : Var) : (nb078_alpha_dummy_430 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv) := by
  simpa only [nb078_alpha_dummy_430] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_427 g)) (Class.cv (nb078_alpha_dummy_428 g)))).fv) 0

theorem nb078_fresh_1472 : (nb078_alpha_dummy_465) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv) := by
  simpa only [nb078_alpha_dummy_465] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv) 0

theorem nb078_fresh_1473 (g : Var) : (nb078_alpha_dummy_466 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv) := by
  simpa only [nb078_alpha_dummy_466] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv) 0

theorem nb078_fresh_1474 : (nb078_alpha_dummy_505) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv) := by
  simpa only [nb078_alpha_dummy_505] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv) 0

theorem nb078_fresh_1475 (g : Var) : (nb078_alpha_dummy_506 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv) := by
  simpa only [nb078_alpha_dummy_506] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv) 0

theorem nb078_fresh_1476 : (nb078_alpha_dummy_549) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv) := by
  simpa only [nb078_alpha_dummy_549] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv) 0

theorem nb078_fresh_1477 (g : Var) : (nb078_alpha_dummy_550 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv) := by
  simpa only [nb078_alpha_dummy_550] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv) 0

theorem nb078_fresh_1478 : (nb078_alpha_dummy_597) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv) := by
  simpa only [nb078_alpha_dummy_597] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_592)) (Class.cv (nb078_alpha_dummy_593)))).fv) 0

theorem nb078_fresh_1479 (g : Var) : (nb078_alpha_dummy_598 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv) := by
  simpa only [nb078_alpha_dummy_598] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_595 g)) (Class.cv (nb078_alpha_dummy_596 g)))).fv) 0

theorem nb078_fresh_1480 : (nb078_alpha_dummy_633) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv) := by
  simpa only [nb078_alpha_dummy_633] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_628)) (Class.cv (nb078_alpha_dummy_629)))).fv) 0

theorem nb078_fresh_1481 (g : Var) : (nb078_alpha_dummy_634 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv) := by
  simpa only [nb078_alpha_dummy_634] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_631 g)) (Class.cv (nb078_alpha_dummy_632 g)))).fv) 0

theorem nb078_fresh_1482 : (nb078_alpha_dummy_675) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv) := by
  simpa only [nb078_alpha_dummy_675] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_670)) (Class.cv (nb078_alpha_dummy_671)))).fv) 0

theorem nb078_fresh_1483 (g : Var) : (nb078_alpha_dummy_676 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv) := by
  simpa only [nb078_alpha_dummy_676] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_673 g)) (Class.cv (nb078_alpha_dummy_674 g)))).fv) 0

theorem nb078_fresh_1484 : (nb078_alpha_dummy_711) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv) := by
  simpa only [nb078_alpha_dummy_711] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_706)) (Class.cv (nb078_alpha_dummy_707)))).fv) 0

theorem nb078_fresh_1485 (g : Var) : (nb078_alpha_dummy_712 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv) := by
  simpa only [nb078_alpha_dummy_712] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_709 g)) (Class.cv (nb078_alpha_dummy_710 g)))).fv) 0

theorem nb078_fresh_1486 : (nb078_alpha_dummy_747) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv) := by
  simpa only [nb078_alpha_dummy_747] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_742)) (Class.cv (nb078_alpha_dummy_743)))).fv) 0

theorem nb078_fresh_1487 (g : Var) : (nb078_alpha_dummy_748 g) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv) := by
  simpa only [nb078_alpha_dummy_748] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_745 g)) (Class.cv (nb078_alpha_dummy_746 g)))).fv) 0

theorem nb078_fresh_1488 : (nb078_alpha_dummy_795) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv) := by
  simpa only [nb078_alpha_dummy_795] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_790)) (Class.cv (nb078_alpha_dummy_791)))).fv) 0

theorem nb078_fresh_1489 (h : Var) : (nb078_alpha_dummy_796 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv) := by
  simpa only [nb078_alpha_dummy_796] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_793 h)) (Class.cv (nb078_alpha_dummy_794 h)))).fv) 0

theorem nb078_fresh_1490 : (nb078_alpha_dummy_831) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv) := by
  simpa only [nb078_alpha_dummy_831] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_826)) (Class.cv (nb078_alpha_dummy_827)))).fv) 0

theorem nb078_fresh_1491 (h : Var) : (nb078_alpha_dummy_832 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv) := by
  simpa only [nb078_alpha_dummy_832] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_829 h)) (Class.cv (nb078_alpha_dummy_830 h)))).fv) 0

theorem nb078_fresh_1492 : (nb078_alpha_dummy_873) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv) := by
  simpa only [nb078_alpha_dummy_873] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv) 0

theorem nb078_fresh_1493 (h : Var) : (nb078_alpha_dummy_874 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv) := by
  simpa only [nb078_alpha_dummy_874] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h)) (Class.cv (nb078_alpha_dummy_872 h)))).fv) 0

theorem nb078_fresh_1494 : (nb078_alpha_dummy_909) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv) := by
  simpa only [nb078_alpha_dummy_909] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv) 0

theorem nb078_fresh_1495 (h : Var) : (nb078_alpha_dummy_910 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv) := by
  simpa only [nb078_alpha_dummy_910] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv) 0

theorem nb078_fresh_1496 : (nb078_alpha_dummy_945) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv) := by
  simpa only [nb078_alpha_dummy_945] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv) 0

theorem nb078_fresh_1497 (h : Var) : (nb078_alpha_dummy_946 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv) := by
  simpa only [nb078_alpha_dummy_946] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv) 0

theorem nb078_fresh_1498 : (nb078_alpha_dummy_985) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv) := by
  simpa only [nb078_alpha_dummy_985] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv) 0

theorem nb078_fresh_1499 (h : Var) : (nb078_alpha_dummy_986 h) ∉ (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv) := by
  simpa only [nb078_alpha_dummy_986] using freshVar_not_mem (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv) 0

theorem nb078_fresh_1500 : (nb078_alpha_dummy_005) ∉ (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_005] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv) 0

theorem nb078_fresh_1501 : (nb078_alpha_dummy_283) ∉ (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_283] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (syn_cid))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
