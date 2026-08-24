import NAR4C078C001Part020

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

theorem nb078_fresh_1502 : (nb078_alpha_dummy_763) ∉ (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_763] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv) 0

theorem nb078_fresh_1503 (f : Var) : (nb078_alpha_dummy_006 f) ∉ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_006] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0

theorem nb078_fresh_1504 (g : Var) : (nb078_alpha_dummy_284 g) ∉ (((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_284] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv g) (syn_ccnv (Class.cv g))) (syn_cid))).fv) 0

theorem nb078_fresh_1505 (h : Var) : (nb078_alpha_dummy_764 h) ∉ (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_764] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) 0

theorem nb078_fresh_1506 : (nb078_alpha_dummy_565) ∉ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_565] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))) (syn_cid))).fv) 0

theorem nb078_fresh_1507 : (nb078_alpha_dummy_1045) ∉ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_1045] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv) 0

theorem nb078_fresh_1508 (g : Var) : (nb078_alpha_dummy_566 g) ∉ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g)))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_566] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g)))) (syn_cid))).fv) 0

theorem nb078_fresh_1509 (h : Var) : (nb078_alpha_dummy_1046 h) ∉ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv) := by
  simpa only [nb078_alpha_dummy_1046] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv) 0

theorem nb078_fresh_1510 : (nb078_alpha_dummy_521) ∉ (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv) := by
  simpa only [nb078_alpha_dummy_521] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv) 0

theorem nb078_fresh_1511 : (nb078_alpha_dummy_1001) ∉ (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv) := by
  simpa only [nb078_alpha_dummy_1001] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv) 0

theorem nb078_fresh_1512 (x : Var) (g : Var) : (nb078_alpha_dummy_522 x g) ∉ (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv) := by
  simpa only [nb078_alpha_dummy_522] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv) 0

theorem nb078_fresh_1513 (y : Var) (h : Var) : (nb078_alpha_dummy_1002 y h) ∉ (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv) := by
  simpa only [nb078_alpha_dummy_1002] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv) 0

theorem nb078_fresh_1514 : (nb078_alpha_dummy_051) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv) := by
  simpa only [nb078_alpha_dummy_051] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv) 0

theorem nb078_fresh_1515 (f : Var) : (nb078_alpha_dummy_052 f) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv) := by
  simpa only [nb078_alpha_dummy_052] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv) 0

theorem nb078_fresh_1516 : (nb078_alpha_dummy_087) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv) := by
  simpa only [nb078_alpha_dummy_087] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv) 0

theorem nb078_fresh_1517 (f : Var) : (nb078_alpha_dummy_088 f) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv) := by
  simpa only [nb078_alpha_dummy_088] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv) 0

theorem nb078_fresh_1518 : (nb078_alpha_dummy_129) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv) := by
  simpa only [nb078_alpha_dummy_129] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv) 0

theorem nb078_fresh_1519 (f : Var) : (nb078_alpha_dummy_130 f) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv) := by
  simpa only [nb078_alpha_dummy_130] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv) 0

theorem nb078_fresh_1520 : (nb078_alpha_dummy_1043) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv) := by
  simpa only [nb078_alpha_dummy_1043] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv) 0

theorem nb078_fresh_1521 (h : Var) : (nb078_alpha_dummy_1044 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1044] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv) 0

theorem nb078_fresh_1522 : (nb078_alpha_dummy_1091) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv) := by
  simpa only [nb078_alpha_dummy_1091] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv) 0

theorem nb078_fresh_1523 (h : Var) : (nb078_alpha_dummy_1092 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1092] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv) 0

theorem nb078_fresh_1524 : (nb078_alpha_dummy_1127) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv) := by
  simpa only [nb078_alpha_dummy_1127] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv) 0

theorem nb078_fresh_1525 (h : Var) : (nb078_alpha_dummy_1128 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1128] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv) 0

theorem nb078_fresh_1526 : (nb078_alpha_dummy_1169) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv) := by
  simpa only [nb078_alpha_dummy_1169] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv) 0

theorem nb078_fresh_1527 (h : Var) : (nb078_alpha_dummy_1170 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1170] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv) 0

theorem nb078_fresh_1528 : (nb078_alpha_dummy_1205) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv) := by
  simpa only [nb078_alpha_dummy_1205] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv) 0

theorem nb078_fresh_1529 (h : Var) : (nb078_alpha_dummy_1206 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1206] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv) 0

theorem nb078_fresh_1530 : (nb078_alpha_dummy_1241) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv) := by
  simpa only [nb078_alpha_dummy_1241] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv) 0

theorem nb078_fresh_1531 (h : Var) : (nb078_alpha_dummy_1242 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1242] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv) 0

theorem nb078_fresh_1532 : (nb078_alpha_dummy_165) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv) := by
  simpa only [nb078_alpha_dummy_165] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv) 0

theorem nb078_fresh_1533 (f : Var) : (nb078_alpha_dummy_166 f) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv) := by
  simpa only [nb078_alpha_dummy_166] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv) 0

theorem nb078_fresh_1534 : (nb078_alpha_dummy_201) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv) := by
  simpa only [nb078_alpha_dummy_201] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv) 0

theorem nb078_fresh_1535 (f : Var) : (nb078_alpha_dummy_202 f) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv) := by
  simpa only [nb078_alpha_dummy_202] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv) 0

theorem nb078_fresh_1536 : (nb078_alpha_dummy_241) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv) := by
  simpa only [nb078_alpha_dummy_241] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv) 0

theorem nb078_fresh_1537 (f : Var) : (nb078_alpha_dummy_242 f) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv) := by
  simpa only [nb078_alpha_dummy_242] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv) 0

theorem nb078_fresh_1538 : (nb078_alpha_dummy_281) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv) := by
  simpa only [nb078_alpha_dummy_281] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv) 0

theorem nb078_fresh_1539 (f : Var) : (nb078_alpha_dummy_282 f) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv) := by
  simpa only [nb078_alpha_dummy_282] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv) 0

theorem nb078_fresh_1540 : (nb078_alpha_dummy_329) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv) := by
  simpa only [nb078_alpha_dummy_329] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_296)))).fv) 0

theorem nb078_fresh_1541 (g : Var) : (nb078_alpha_dummy_330 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv) := by
  simpa only [nb078_alpha_dummy_330] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))).fv) 0

theorem nb078_fresh_1542 : (nb078_alpha_dummy_365) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv) := by
  simpa only [nb078_alpha_dummy_365] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_332)))).fv) 0

theorem nb078_fresh_1543 (g : Var) : (nb078_alpha_dummy_366 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv) := by
  simpa only [nb078_alpha_dummy_366] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))).fv) 0

theorem nb078_fresh_1544 : (nb078_alpha_dummy_407) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv) := by
  simpa only [nb078_alpha_dummy_407] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_374)))).fv) 0

theorem nb078_fresh_1545 (g : Var) : (nb078_alpha_dummy_408 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv) := by
  simpa only [nb078_alpha_dummy_408] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))).fv) 0

theorem nb078_fresh_1546 : (nb078_alpha_dummy_443) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv) := by
  simpa only [nb078_alpha_dummy_443] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_410)))).fv) 0

theorem nb078_fresh_1547 (g : Var) : (nb078_alpha_dummy_444 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv) := by
  simpa only [nb078_alpha_dummy_444] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))).fv) 0

theorem nb078_fresh_1548 : (nb078_alpha_dummy_479) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv) := by
  simpa only [nb078_alpha_dummy_479] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv) 0

theorem nb078_fresh_1549 (g : Var) : (nb078_alpha_dummy_480 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv) := by
  simpa only [nb078_alpha_dummy_480] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv) 0

theorem nb078_fresh_1550 : (nb078_alpha_dummy_519) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv) := by
  simpa only [nb078_alpha_dummy_519] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv) 0

theorem nb078_fresh_1551 (g : Var) : (nb078_alpha_dummy_520 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv) := by
  simpa only [nb078_alpha_dummy_520] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv) 0

theorem nb078_fresh_1552 : (nb078_alpha_dummy_563) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv) := by
  simpa only [nb078_alpha_dummy_563] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv) 0

theorem nb078_fresh_1553 (g : Var) : (nb078_alpha_dummy_564 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv) := by
  simpa only [nb078_alpha_dummy_564] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv) 0

theorem nb078_fresh_1554 : (nb078_alpha_dummy_611) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv) := by
  simpa only [nb078_alpha_dummy_611] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_578)))).fv) 0

theorem nb078_fresh_1555 (g : Var) : (nb078_alpha_dummy_612 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv) := by
  simpa only [nb078_alpha_dummy_612] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))).fv) 0

theorem nb078_fresh_1556 : (nb078_alpha_dummy_647) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv) := by
  simpa only [nb078_alpha_dummy_647] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_614)))).fv) 0

theorem nb078_fresh_1557 (g : Var) : (nb078_alpha_dummy_648 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv) := by
  simpa only [nb078_alpha_dummy_648] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))).fv) 0

theorem nb078_fresh_1558 : (nb078_alpha_dummy_689) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv) := by
  simpa only [nb078_alpha_dummy_689] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_656)))).fv) 0

theorem nb078_fresh_1559 (g : Var) : (nb078_alpha_dummy_690 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv) := by
  simpa only [nb078_alpha_dummy_690] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))).fv) 0

theorem nb078_fresh_1560 : (nb078_alpha_dummy_725) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv) := by
  simpa only [nb078_alpha_dummy_725] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_692)))).fv) 0

theorem nb078_fresh_1561 (g : Var) : (nb078_alpha_dummy_726 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv) := by
  simpa only [nb078_alpha_dummy_726] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))).fv) 0

theorem nb078_fresh_1562 : (nb078_alpha_dummy_761) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv) := by
  simpa only [nb078_alpha_dummy_761] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_728)))).fv) 0

theorem nb078_fresh_1563 (g : Var) : (nb078_alpha_dummy_762 g) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv) := by
  simpa only [nb078_alpha_dummy_762] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))).fv) 0

theorem nb078_fresh_1564 : (nb078_alpha_dummy_809) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv) := by
  simpa only [nb078_alpha_dummy_809] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_776)))).fv) 0

theorem nb078_fresh_1565 (h : Var) : (nb078_alpha_dummy_810 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv) := by
  simpa only [nb078_alpha_dummy_810] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))).fv) 0

theorem nb078_fresh_1566 : (nb078_alpha_dummy_845) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv) := by
  simpa only [nb078_alpha_dummy_845] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_812)))).fv) 0

theorem nb078_fresh_1567 (h : Var) : (nb078_alpha_dummy_846 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv) := by
  simpa only [nb078_alpha_dummy_846] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))).fv) 0

theorem nb078_fresh_1568 : (nb078_alpha_dummy_887) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv) := by
  simpa only [nb078_alpha_dummy_887] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv) 0

theorem nb078_fresh_1569 (h : Var) : (nb078_alpha_dummy_888 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv) := by
  simpa only [nb078_alpha_dummy_888] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv) 0

theorem nb078_fresh_1570 : (nb078_alpha_dummy_923) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv) := by
  simpa only [nb078_alpha_dummy_923] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv) 0

theorem nb078_fresh_1571 (h : Var) : (nb078_alpha_dummy_924 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv) := by
  simpa only [nb078_alpha_dummy_924] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv) 0

theorem nb078_fresh_1572 : (nb078_alpha_dummy_959) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv) := by
  simpa only [nb078_alpha_dummy_959] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv) 0

theorem nb078_fresh_1573 (h : Var) : (nb078_alpha_dummy_960 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv) := by
  simpa only [nb078_alpha_dummy_960] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv) 0

theorem nb078_fresh_1574 : (nb078_alpha_dummy_999) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv) := by
  simpa only [nb078_alpha_dummy_999] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv) 0

theorem nb078_fresh_1575 (h : Var) : (nb078_alpha_dummy_1000 h) ∉ (((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1000] using freshVar_not_mem (((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv) 0

theorem nb078_fresh_1576 : (nb078_alpha_dummy_523) ∉ (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((Class.cv (nb078_alpha_dummy_003))).fv) := by
  simpa only [nb078_alpha_dummy_523] using freshVar_not_mem (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((Class.cv (nb078_alpha_dummy_003))).fv) 0

theorem nb078_fresh_1577 : (nb078_alpha_dummy_1003) ∉ (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((Class.cv (nb078_alpha_dummy_004))).fv) := by
  simpa only [nb078_alpha_dummy_1003] using freshVar_not_mem (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((Class.cv (nb078_alpha_dummy_004))).fv) 0

theorem nb078_fresh_1578 (x : Var) (g : Var) : (nb078_alpha_dummy_524 x g) ∉ (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb078_alpha_dummy_524] using freshVar_not_mem (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) 0

theorem nb078_fresh_1579 (y : Var) (h : Var) : (nb078_alpha_dummy_1004 y h) ∉ (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb078_alpha_dummy_1004] using freshVar_not_mem (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) 0

theorem nb078_fresh_1580 : (nb078_alpha_dummy_015) ∉ (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))) (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) := by
  simpa only [nb078_alpha_dummy_015] using freshVar_not_mem (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))) (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) 0

theorem nb078_fresh_1581 (f : Var) : (nb078_alpha_dummy_016 f) ∉ (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb078_alpha_dummy_014 f))) (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_013 f)))))).fv) := by
  simpa only [nb078_alpha_dummy_016] using freshVar_not_mem (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb078_alpha_dummy_014 f))) (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_013 f)))))).fv) 0

theorem nb078_fresh_1582 : (nb078_alpha_dummy_093) ∉ (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_089)))).fv) := by
  simpa only [nb078_alpha_dummy_093] using freshVar_not_mem (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_089)))).fv) 0

theorem nb078_fresh_1583 (f : Var) : (nb078_alpha_dummy_094 f) ∉ (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_091 f)))).fv) := by
  simpa only [nb078_alpha_dummy_094] using freshVar_not_mem (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_091 f)))).fv) 0

theorem nb078_fresh_1584 : (nb078_alpha_dummy_1055) ∉ (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (Class.cv (nb078_alpha_dummy_1051))) (syn_wbr (Class.cv (nb078_alpha_dummy_1051)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_1050)))))).fv) := by
  simpa only [nb078_alpha_dummy_1055] using freshVar_not_mem (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (Class.cv (nb078_alpha_dummy_1051))) (syn_wbr (Class.cv (nb078_alpha_dummy_1051)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_1050)))))).fv) 0

theorem nb078_fresh_1585 (h : Var) : (nb078_alpha_dummy_1056 h) ∉ (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) := by
  simpa only [nb078_alpha_dummy_1056] using freshVar_not_mem (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) 0

theorem nb078_fresh_1586 : (nb078_alpha_dummy_1133) ∉ (({(nb078_alpha_dummy_1129)} : Finset Var) ∪ ({(nb078_alpha_dummy_1130)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_1130)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_1129)))).fv) := by
  simpa only [nb078_alpha_dummy_1133] using freshVar_not_mem (({(nb078_alpha_dummy_1129)} : Finset Var) ∪ ({(nb078_alpha_dummy_1130)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_1130)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_1129)))).fv) 0

theorem nb078_fresh_1587 (h : Var) : (nb078_alpha_dummy_1134 h) ∉ (({(nb078_alpha_dummy_1131 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_1132 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_1131 h)))).fv) := by
  simpa only [nb078_alpha_dummy_1134] using freshVar_not_mem (({(nb078_alpha_dummy_1131 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_1132 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_1131 h)))).fv) 0

theorem nb078_fresh_1588 : (nb078_alpha_dummy_293) ∉ (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) := by
  simpa only [nb078_alpha_dummy_293] using freshVar_not_mem (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) 0

theorem nb078_fresh_1589 (g : Var) : (nb078_alpha_dummy_294 g) ∉ (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_292 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_291 g)))))).fv) := by
  simpa only [nb078_alpha_dummy_294] using freshVar_not_mem (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_292 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_291 g)))))).fv) 0

theorem nb078_fresh_1590 : (nb078_alpha_dummy_371) ∉ (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_367)))).fv) := by
  simpa only [nb078_alpha_dummy_371] using freshVar_not_mem (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_367)))).fv) 0

theorem nb078_fresh_1591 (g : Var) : (nb078_alpha_dummy_372 g) ∉ (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_369 g)))).fv) := by
  simpa only [nb078_alpha_dummy_372] using freshVar_not_mem (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_369 g)))).fv) 0

theorem nb078_fresh_1592 : (nb078_alpha_dummy_575) ∉ (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_570)))))).fv) := by
  simpa only [nb078_alpha_dummy_575] using freshVar_not_mem (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_570)))))).fv) 0

theorem nb078_fresh_1593 (g : Var) : (nb078_alpha_dummy_576 g) ∉ (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_572 g)) (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_573 g)))))).fv) := by
  simpa only [nb078_alpha_dummy_576] using freshVar_not_mem (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_572 g)) (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_573 g)))))).fv) 0

theorem nb078_fresh_1594 : (nb078_alpha_dummy_653) ∉ (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_650)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_649)))).fv) := by
  simpa only [nb078_alpha_dummy_653] using freshVar_not_mem (({(nb078_alpha_dummy_649)} : Finset Var) ∪ ({(nb078_alpha_dummy_650)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_650)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_649)))).fv) 0

theorem nb078_fresh_1595 (g : Var) : (nb078_alpha_dummy_654 g) ∉ (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_651 g)))).fv) := by
  simpa only [nb078_alpha_dummy_654] using freshVar_not_mem (({(nb078_alpha_dummy_651 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_652 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_652 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_651 g)))).fv) 0

theorem nb078_fresh_1596 : (nb078_alpha_dummy_773) ∉ (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) := by
  simpa only [nb078_alpha_dummy_773] using freshVar_not_mem (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) 0

theorem nb078_fresh_1597 (h : Var) : (nb078_alpha_dummy_774 h) ∉ (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_772 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_771 h)))))).fv) := by
  simpa only [nb078_alpha_dummy_774] using freshVar_not_mem (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb078_alpha_dummy_772 h))) (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_771 h)))))).fv) 0

theorem nb078_fresh_1598 : (nb078_alpha_dummy_851) ∉ (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_847)))).fv) := by
  simpa only [nb078_alpha_dummy_851] using freshVar_not_mem (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_847)))).fv) 0

theorem nb078_fresh_1599 (h : Var) : (nb078_alpha_dummy_852 h) ∉ (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_849 h)))).fv) := by
  simpa only [nb078_alpha_dummy_852] using freshVar_not_mem (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h) (Class.cv (nb078_alpha_dummy_849 h)))).fv) 0

theorem nb078_fresh_1600 : (nb078_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb078_fresh_1601 : (nb078_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb078_fresh_1602 : (nb078_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb078_fresh_1603 : (nb078_alpha_dummy_003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb078_fresh_1604 : (nb078_alpha_dummy_004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb078_alpha_dummy_004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb078_distinct_1605 : (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_001) := by
  simpa only [nb078_alpha_dummy_000, nb078_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1606 : (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_002) := by
  simpa only [nb078_alpha_dummy_000, nb078_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1607 : (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_003) := by
  simpa only [nb078_alpha_dummy_000, nb078_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb078_distinct_1608 : (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_004) := by
  simpa only [nb078_alpha_dummy_000, nb078_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb078_distinct_1609 : (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_002) := by
  simpa only [nb078_alpha_dummy_001, nb078_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb078_distinct_1610 : (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_003) := by
  simpa only [nb078_alpha_dummy_001, nb078_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb078_distinct_1611 : (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_004) := by
  simpa only [nb078_alpha_dummy_001, nb078_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb078_distinct_1612 : (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_003) := by
  simpa only [nb078_alpha_dummy_002, nb078_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb078_distinct_1613 : (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_004) := by
  simpa only [nb078_alpha_dummy_002, nb078_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb078_distinct_1614 : (nb078_alpha_dummy_003) ≠ (nb078_alpha_dummy_004) := by
  simpa only [nb078_alpha_dummy_003, nb078_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb078_support_mem_0000 : (nb078_alpha_dummy_009) ∈ (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))) (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0001 (f : Var) : (nb078_alpha_dummy_012 f) ∈ (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb078_alpha_dummy_014 f))) (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_013 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0002 : (nb078_alpha_dummy_010) ∈ (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))) (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011)) (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0003 (f : Var) : (nb078_alpha_dummy_013 f) ∈ (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb078_alpha_dummy_014 f))) (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f) (Class.cv (nb078_alpha_dummy_013 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0004 : (nb078_alpha_dummy_009) ∈ (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0005 : (nb078_alpha_dummy_009) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0006 (f : Var) : (nb078_alpha_dummy_012 f) ∈ (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0007 (f : Var) : (nb078_alpha_dummy_012 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0008 : (nb078_alpha_dummy_009) ∈ (((Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0004) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0009 (f : Var) : (nb078_alpha_dummy_012 f) ∈ (((Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0006 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0010 : (nb078_alpha_dummy_018) ∈ (((Class.cv (nb078_alpha_dummy_018))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0011 (f : Var) : (nb078_alpha_dummy_020 f) ∈ (((Class.cv (nb078_alpha_dummy_020 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0012 : (nb078_alpha_dummy_025) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_025)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_025)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_025))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0013 (f : Var) : (nb078_alpha_dummy_027 f) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_027 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_027 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_027 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0014 : (nb078_alpha_dummy_025) ∈ (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0015 (f : Var) : (nb078_alpha_dummy_027 f) ∈ (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0016 : (nb078_alpha_dummy_032) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0017 (f : Var) : (nb078_alpha_dummy_035 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0018 : (nb078_alpha_dummy_032) ∈ (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0019 (f : Var) : (nb078_alpha_dummy_035 f) ∈ (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0020 : (nb078_alpha_dummy_033) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_032)) (Class.cv (nb078_alpha_dummy_033)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0021 (f : Var) : (nb078_alpha_dummy_036 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_035 f)) (Class.cv (nb078_alpha_dummy_036 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0022 : (nb078_alpha_dummy_033) ∈ (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0023 (f : Var) : (nb078_alpha_dummy_036 f) ∈ (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0024 : (nb078_alpha_dummy_032) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_032)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_033)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0025 (f : Var) : (nb078_alpha_dummy_035 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_035 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_036 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0026 : (nb078_alpha_dummy_032) ∈ (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_032))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0027 (f : Var) : (nb078_alpha_dummy_035 f) ∈ (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_035 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0028 : (nb078_alpha_dummy_033) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_032)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_033)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0029 (f : Var) : (nb078_alpha_dummy_036 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_035 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_036 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0030 : (nb078_alpha_dummy_033) ∈ (((Class.cv (nb078_alpha_dummy_033))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0031 (f : Var) : (nb078_alpha_dummy_036 f) ∈ (((Class.cv (nb078_alpha_dummy_036 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0032 : (nb078_alpha_dummy_010) ∈ (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
