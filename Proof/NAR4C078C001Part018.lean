import NAR4C078C001Part017

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

theorem nb078_fresh_1154 : (nb078_alpha_dummy_343) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_339)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_339)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_339))).fv) := by
  simpa only [nb078_alpha_dummy_343] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_339)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_339)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_339))).fv) 0

theorem nb078_fresh_1155 (g : Var) : (nb078_alpha_dummy_344 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_341 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_341 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_341 g))).fv) := by
  simpa only [nb078_alpha_dummy_344] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_341 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_341 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_341 g))).fv) 0

theorem nb078_fresh_1156 : (nb078_alpha_dummy_385) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_381)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_381)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_381))).fv) := by
  simpa only [nb078_alpha_dummy_385] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_381)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_381)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_381))).fv) 0

theorem nb078_fresh_1157 (g : Var) : (nb078_alpha_dummy_386 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_383 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_383 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_383 g))).fv) := by
  simpa only [nb078_alpha_dummy_386] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_383 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_383 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_383 g))).fv) 0

theorem nb078_fresh_1158 : (nb078_alpha_dummy_421) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_417)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_417)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_417))).fv) := by
  simpa only [nb078_alpha_dummy_421] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_417)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_417)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_417))).fv) 0

theorem nb078_fresh_1159 (g : Var) : (nb078_alpha_dummy_422 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_419 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_419 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_419 g))).fv) := by
  simpa only [nb078_alpha_dummy_422] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_419 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_419 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_419 g))).fv) 0

theorem nb078_fresh_1160 : (nb078_alpha_dummy_457) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_453)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_453)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_453))).fv) := by
  simpa only [nb078_alpha_dummy_457] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_453)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_453)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_453))).fv) 0

theorem nb078_fresh_1161 (g : Var) : (nb078_alpha_dummy_458 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_455 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_455 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_455 g))).fv) := by
  simpa only [nb078_alpha_dummy_458] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_455 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_455 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_455 g))).fv) 0

theorem nb078_fresh_1162 : (nb078_alpha_dummy_497) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_493)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_493)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_493))).fv) := by
  simpa only [nb078_alpha_dummy_497] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_493)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_493)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_493))).fv) 0

theorem nb078_fresh_1163 (g : Var) : (nb078_alpha_dummy_498 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_495 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_495 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_495 g))).fv) := by
  simpa only [nb078_alpha_dummy_498] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_495 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_495 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_495 g))).fv) 0

theorem nb078_fresh_1164 : (nb078_alpha_dummy_541) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_537)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_537)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_537))).fv) := by
  simpa only [nb078_alpha_dummy_541] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_537)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_537)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_537))).fv) 0

theorem nb078_fresh_1165 (g : Var) : (nb078_alpha_dummy_542 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_539 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_539 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_539 g))).fv) := by
  simpa only [nb078_alpha_dummy_542] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_539 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_539 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_539 g))).fv) 0

theorem nb078_fresh_1166 : (nb078_alpha_dummy_589) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_585)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_585)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_585))).fv) := by
  simpa only [nb078_alpha_dummy_589] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_585)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_585)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_585))).fv) 0

theorem nb078_fresh_1167 (g : Var) : (nb078_alpha_dummy_590 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_587 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_587 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_587 g))).fv) := by
  simpa only [nb078_alpha_dummy_590] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_587 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_587 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_587 g))).fv) 0

theorem nb078_fresh_1168 : (nb078_alpha_dummy_625) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_621)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_621)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_621))).fv) := by
  simpa only [nb078_alpha_dummy_625] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_621)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_621)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_621))).fv) 0

theorem nb078_fresh_1169 (g : Var) : (nb078_alpha_dummy_626 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_623 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_623 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_623 g))).fv) := by
  simpa only [nb078_alpha_dummy_626] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_623 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_623 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_623 g))).fv) 0

theorem nb078_fresh_1170 : (nb078_alpha_dummy_667) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_663)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_663)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_663))).fv) := by
  simpa only [nb078_alpha_dummy_667] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_663)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_663)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_663))).fv) 0

theorem nb078_fresh_1171 (g : Var) : (nb078_alpha_dummy_668 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_665 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_665 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_665 g))).fv) := by
  simpa only [nb078_alpha_dummy_668] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_665 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_665 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_665 g))).fv) 0

theorem nb078_fresh_1172 : (nb078_alpha_dummy_703) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_699)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_699)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_699))).fv) := by
  simpa only [nb078_alpha_dummy_703] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_699)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_699)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_699))).fv) 0

theorem nb078_fresh_1173 (g : Var) : (nb078_alpha_dummy_704 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_701 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_701 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_701 g))).fv) := by
  simpa only [nb078_alpha_dummy_704] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_701 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_701 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_701 g))).fv) 0

theorem nb078_fresh_1174 : (nb078_alpha_dummy_739) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_735)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_735)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_735))).fv) := by
  simpa only [nb078_alpha_dummy_739] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_735)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_735)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_735))).fv) 0

theorem nb078_fresh_1175 (g : Var) : (nb078_alpha_dummy_740 g) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_737 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_737 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_737 g))).fv) := by
  simpa only [nb078_alpha_dummy_740] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_737 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_737 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_737 g))).fv) 0

theorem nb078_fresh_1176 : (nb078_alpha_dummy_787) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_783)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_783)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_783))).fv) := by
  simpa only [nb078_alpha_dummy_787] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_783)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_783)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_783))).fv) 0

theorem nb078_fresh_1177 (h : Var) : (nb078_alpha_dummy_788 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_785 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_785 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_785 h))).fv) := by
  simpa only [nb078_alpha_dummy_788] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_785 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_785 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_785 h))).fv) 0

theorem nb078_fresh_1178 : (nb078_alpha_dummy_823) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_819)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_819)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_819))).fv) := by
  simpa only [nb078_alpha_dummy_823] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_819)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_819)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_819))).fv) 0

theorem nb078_fresh_1179 (h : Var) : (nb078_alpha_dummy_824 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_821 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_821 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_821 h))).fv) := by
  simpa only [nb078_alpha_dummy_824] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_821 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_821 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_821 h))).fv) 0

theorem nb078_fresh_1180 : (nb078_alpha_dummy_865) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_861)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_861)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_861))).fv) := by
  simpa only [nb078_alpha_dummy_865] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_861)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_861)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_861))).fv) 0

theorem nb078_fresh_1181 (h : Var) : (nb078_alpha_dummy_866 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_863 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_863 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_863 h))).fv) := by
  simpa only [nb078_alpha_dummy_866] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_863 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_863 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_863 h))).fv) 0

theorem nb078_fresh_1182 : (nb078_alpha_dummy_901) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_897)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_897)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_897))).fv) := by
  simpa only [nb078_alpha_dummy_901] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_897)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_897)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_897))).fv) 0

theorem nb078_fresh_1183 (h : Var) : (nb078_alpha_dummy_902 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_899 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_899 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_899 h))).fv) := by
  simpa only [nb078_alpha_dummy_902] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_899 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_899 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_899 h))).fv) 0

theorem nb078_fresh_1184 : (nb078_alpha_dummy_937) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_933)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_933)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_933))).fv) := by
  simpa only [nb078_alpha_dummy_937] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_933)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_933)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_933))).fv) 0

theorem nb078_fresh_1185 (h : Var) : (nb078_alpha_dummy_938 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_935 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_935 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_935 h))).fv) := by
  simpa only [nb078_alpha_dummy_938] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_935 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_935 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_935 h))).fv) 0

theorem nb078_fresh_1186 : (nb078_alpha_dummy_977) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_973)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_973)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_973))).fv) := by
  simpa only [nb078_alpha_dummy_977] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_973)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_973)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_973))).fv) 0

theorem nb078_fresh_1187 (h : Var) : (nb078_alpha_dummy_978 h) ∉ (((Wff.classMem (Class.cv (nb078_alpha_dummy_975 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_975 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_975 h))).fv) := by
  simpa only [nb078_alpha_dummy_978] using freshVar_not_mem (((Wff.classMem (Class.cv (nb078_alpha_dummy_975 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_975 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_975 h))).fv) 0

theorem nb078_fresh_1188 : (nb078_alpha_dummy_203) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_203] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1189 : (nb078_alpha_dummy_204) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_204] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1190 : (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_204) := by
  simpa only [nb078_alpha_dummy_203, nb078_alpha_dummy_204] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1191 : (nb078_alpha_dummy_649) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) := by
  simpa only [nb078_alpha_dummy_649] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 0

theorem nb078_fresh_1192 : (nb078_alpha_dummy_650) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) := by
  simpa only [nb078_alpha_dummy_650] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 1

theorem nb078_distinct_1193 : (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_650) := by
  simpa only [nb078_alpha_dummy_649, nb078_alpha_dummy_650] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1194 : (nb078_alpha_dummy_569) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) := by
  simpa only [nb078_alpha_dummy_569] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) 0

theorem nb078_fresh_1195 : (nb078_alpha_dummy_570) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) := by
  simpa only [nb078_alpha_dummy_570] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) 1

theorem nb078_fresh_1196 : (nb078_alpha_dummy_571) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) := by
  simpa only [nb078_alpha_dummy_571] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) 2

theorem nb078_distinct_1197 : (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_570) := by
  simpa only [nb078_alpha_dummy_569, nb078_alpha_dummy_570] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1198 : (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_571) := by
  simpa only [nb078_alpha_dummy_569, nb078_alpha_dummy_571] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1199 : (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_571) := by
  simpa only [nb078_alpha_dummy_570, nb078_alpha_dummy_571] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1200 : (nb078_alpha_dummy_481) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_481] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1201 : (nb078_alpha_dummy_482) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_482] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1202 : (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_482) := by
  simpa only [nb078_alpha_dummy_481, nb078_alpha_dummy_482] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1203 : (nb078_alpha_dummy_1129) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) := by
  simpa only [nb078_alpha_dummy_1129] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 0

theorem nb078_fresh_1204 : (nb078_alpha_dummy_1130) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) := by
  simpa only [nb078_alpha_dummy_1130] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 1

theorem nb078_distinct_1205 : (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1130) := by
  simpa only [nb078_alpha_dummy_1129, nb078_alpha_dummy_1130] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1206 : (nb078_alpha_dummy_1049) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) := by
  simpa only [nb078_alpha_dummy_1049] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) 0

theorem nb078_fresh_1207 : (nb078_alpha_dummy_1050) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) := by
  simpa only [nb078_alpha_dummy_1050] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) 1

theorem nb078_fresh_1208 : (nb078_alpha_dummy_1051) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) := by
  simpa only [nb078_alpha_dummy_1051] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) 2

theorem nb078_distinct_1209 : (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1050) := by
  simpa only [nb078_alpha_dummy_1049, nb078_alpha_dummy_1050] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1210 : (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1051) := by
  simpa only [nb078_alpha_dummy_1049, nb078_alpha_dummy_1051] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1211 : (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1051) := by
  simpa only [nb078_alpha_dummy_1050, nb078_alpha_dummy_1051] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1212 : (nb078_alpha_dummy_961) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_961] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1213 : (nb078_alpha_dummy_962) ∉ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_962] using freshVar_not_mem (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1214 : (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_962) := by
  simpa only [nb078_alpha_dummy_961, nb078_alpha_dummy_962] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1215 (f : Var) : (nb078_alpha_dummy_205 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_205] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1216 (f : Var) : (nb078_alpha_dummy_206 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_206] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1217 (f : Var) : (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_206 f) := by
  simpa only [nb078_alpha_dummy_205, nb078_alpha_dummy_206] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1218 (g : Var) : (nb078_alpha_dummy_651 g) ∉ (((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_651] using freshVar_not_mem (((syn_ccnv (Class.cv g))).fv) 0

theorem nb078_fresh_1219 (g : Var) : (nb078_alpha_dummy_652 g) ∉ (((syn_ccnv (Class.cv g))).fv) := by
  simpa only [nb078_alpha_dummy_652] using freshVar_not_mem (((syn_ccnv (Class.cv g))).fv) 1

theorem nb078_distinct_1220 (g : Var) : (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_652 g) := by
  simpa only [nb078_alpha_dummy_651, nb078_alpha_dummy_652] using
    (freshVar_injective (((syn_ccnv (Class.cv g))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1221 (g : Var) : (nb078_alpha_dummy_572 g) ∉ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) := by
  simpa only [nb078_alpha_dummy_572] using freshVar_not_mem (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 0

theorem nb078_fresh_1222 (g : Var) : (nb078_alpha_dummy_573 g) ∉ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) := by
  simpa only [nb078_alpha_dummy_573] using freshVar_not_mem (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 1

theorem nb078_fresh_1223 (g : Var) : (nb078_alpha_dummy_574 g) ∉ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) := by
  simpa only [nb078_alpha_dummy_574] using freshVar_not_mem (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) 2

theorem nb078_distinct_1224 (g : Var) : (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_573 g) := by
  simpa only [nb078_alpha_dummy_572, nb078_alpha_dummy_573] using
    (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1225 (g : Var) : (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_574 g) := by
  simpa only [nb078_alpha_dummy_572, nb078_alpha_dummy_574] using
    (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1226 (g : Var) : (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_574 g) := by
  simpa only [nb078_alpha_dummy_573, nb078_alpha_dummy_574] using
    (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1227 (g : Var) : (nb078_alpha_dummy_483 g) ∉ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_483] using freshVar_not_mem (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1228 (g : Var) : (nb078_alpha_dummy_484 g) ∉ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_484] using freshVar_not_mem (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1229 (g : Var) : (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_484 g) := by
  simpa only [nb078_alpha_dummy_483, nb078_alpha_dummy_484] using
    (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1230 (h : Var) : (nb078_alpha_dummy_1131 h) ∉ (((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_1131] using freshVar_not_mem (((syn_ccnv (Class.cv h))).fv) 0

theorem nb078_fresh_1231 (h : Var) : (nb078_alpha_dummy_1132 h) ∉ (((syn_ccnv (Class.cv h))).fv) := by
  simpa only [nb078_alpha_dummy_1132] using freshVar_not_mem (((syn_ccnv (Class.cv h))).fv) 1

theorem nb078_distinct_1232 (h : Var) : (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1132 h) := by
  simpa only [nb078_alpha_dummy_1131, nb078_alpha_dummy_1132] using
    (freshVar_injective (((syn_ccnv (Class.cv h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1233 (h : Var) : (nb078_alpha_dummy_1052 h) ∉ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) := by
  simpa only [nb078_alpha_dummy_1052] using freshVar_not_mem (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 0

theorem nb078_fresh_1234 (h : Var) : (nb078_alpha_dummy_1053 h) ∉ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) := by
  simpa only [nb078_alpha_dummy_1053] using freshVar_not_mem (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 1

theorem nb078_fresh_1235 (h : Var) : (nb078_alpha_dummy_1054 h) ∉ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) := by
  simpa only [nb078_alpha_dummy_1054] using freshVar_not_mem (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 2

theorem nb078_distinct_1236 (h : Var) : (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1053 h) := by
  simpa only [nb078_alpha_dummy_1052, nb078_alpha_dummy_1053] using
    (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_1237 (h : Var) : (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1054 h) := by
  simpa only [nb078_alpha_dummy_1052, nb078_alpha_dummy_1054] using
    (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_1238 (h : Var) : (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1054 h) := by
  simpa only [nb078_alpha_dummy_1053, nb078_alpha_dummy_1054] using
    (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_1239 (h : Var) : (nb078_alpha_dummy_963 h) ∉ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_963] using freshVar_not_mem (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_1240 (h : Var) : (nb078_alpha_dummy_964 h) ∉ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_964] using freshVar_not_mem (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_1241 (h : Var) : (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_964 h) := by
  simpa only [nb078_alpha_dummy_963, nb078_alpha_dummy_964] using
    (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_1242 : (nb078_alpha_dummy_007) ∉ (((syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_007] using freshVar_not_mem (((syn_ccom (Class.cv (nb078_alpha_dummy_000)) (syn_ccnv (Class.cv (nb078_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1243 : (nb078_alpha_dummy_285) ∉ (((syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_285] using freshVar_not_mem (((syn_ccom (Class.cv (nb078_alpha_dummy_001)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1244 : (nb078_alpha_dummy_765) ∉ (((syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_765] using freshVar_not_mem (((syn_ccom (Class.cv (nb078_alpha_dummy_002)) (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1245 (f : Var) : (nb078_alpha_dummy_008 f) ∉ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_008] using freshVar_not_mem (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1246 (g : Var) : (nb078_alpha_dummy_286 g) ∉ (((syn_ccom (Class.cv g) (syn_ccnv (Class.cv g)))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_286] using freshVar_not_mem (((syn_ccom (Class.cv g) (syn_ccnv (Class.cv g)))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1247 (h : Var) : (nb078_alpha_dummy_766 h) ∉ (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_766] using freshVar_not_mem (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1248 : (nb078_alpha_dummy_567) ∉ (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_567] using freshVar_not_mem (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1249 : (nb078_alpha_dummy_1047) ∉ (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_1047] using freshVar_not_mem (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1250 (g : Var) : (nb078_alpha_dummy_568 g) ∉ (((syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_568] using freshVar_not_mem (((syn_ccom (syn_ccnv (Class.cv g)) (syn_ccnv (syn_ccnv (Class.cv g))))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1251 (h : Var) : (nb078_alpha_dummy_1048 h) ∉ (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb078_alpha_dummy_1048] using freshVar_not_mem (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪ ((syn_cid)).fv) 0

theorem nb078_fresh_1252 : (nb078_alpha_dummy_021) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_021] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_017) (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_017)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1253 (f : Var) : (nb078_alpha_dummy_022 f) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_022] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f) (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1254 : (nb078_alpha_dummy_057) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_057] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_053) (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1255 (f : Var) : (nb078_alpha_dummy_058 f) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_058] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f) (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1256 : (nb078_alpha_dummy_099) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_099] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_095) (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_095)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1257 (f : Var) : (nb078_alpha_dummy_100 f) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_100] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f) (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1258 : (nb078_alpha_dummy_1013) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1013] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1259 (h : Var) : (nb078_alpha_dummy_1014 h) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1014] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1260 : (nb078_alpha_dummy_1061) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1061] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1261 (h : Var) : (nb078_alpha_dummy_1062 h) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1062] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1262 : (nb078_alpha_dummy_1097) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1097] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1093) (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1093)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1263 (h : Var) : (nb078_alpha_dummy_1098 h) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1098] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h) (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1264 : (nb078_alpha_dummy_1139) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1139] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1135) (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1135)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1265 (h : Var) : (nb078_alpha_dummy_1140 h) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1140] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h) (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1266 : (nb078_alpha_dummy_1175) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1171) (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1171)) (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1171) (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1171)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1175] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1171) (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1171)) (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1171) (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1171)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1267 (h : Var) : (nb078_alpha_dummy_1176 h) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h) (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h) (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1176] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h) (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h) (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1268 : (nb078_alpha_dummy_1211) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1207) (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1207)) (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1207) (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1207)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1211] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1207) (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1207)) (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1207) (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1207)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1269 (h : Var) : (nb078_alpha_dummy_1212 h) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_1209 h) (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1209 h) (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_1212] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_1209 h) (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1209 h) (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1270 : (nb078_alpha_dummy_135) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_135] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_131) (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089)) (Wff.classEq (Class.cv (nb078_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1271 (f : Var) : (nb078_alpha_dummy_136 f) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_136] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f) (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1272 : (nb078_alpha_dummy_171) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_171] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb078_fresh_1273 (f : Var) : (nb078_alpha_dummy_172 f) ∉ (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb078_alpha_dummy_172] using freshVar_not_mem (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
