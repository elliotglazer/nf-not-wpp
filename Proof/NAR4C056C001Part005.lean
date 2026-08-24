import NAR4C056C001Part004

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

theorem nb056_support_mem_0128 : (nb056_alpha_dummy_128) ∈ (((Class.cv (nb056_alpha_dummy_128))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0129 (f : Var) : (nb056_alpha_dummy_130 f) ∈ (((Class.cv (nb056_alpha_dummy_130 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0130 : (nb056_alpha_dummy_135) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_135)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_135)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_135))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0131 (f : Var) : (nb056_alpha_dummy_137 f) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_137 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_137 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_137 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0132 : (nb056_alpha_dummy_135) ∈ (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0133 (f : Var) : (nb056_alpha_dummy_137 f) ∈ (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0134 : (nb056_alpha_dummy_142) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0135 (f : Var) : (nb056_alpha_dummy_145 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0136 : (nb056_alpha_dummy_142) ∈ (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0137 (f : Var) : (nb056_alpha_dummy_145 f) ∈ (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0138 : (nb056_alpha_dummy_143) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0139 (f : Var) : (nb056_alpha_dummy_146 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0140 : (nb056_alpha_dummy_143) ∈ (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0141 (f : Var) : (nb056_alpha_dummy_146 f) ∈ (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0142 : (nb056_alpha_dummy_142) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0143 (f : Var) : (nb056_alpha_dummy_145 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0144 : (nb056_alpha_dummy_142) ∈ (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_142))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0145 (f : Var) : (nb056_alpha_dummy_145 f) ∈ (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_145 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0146 : (nb056_alpha_dummy_143) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0147 (f : Var) : (nb056_alpha_dummy_146 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0148 : (nb056_alpha_dummy_143) ∈ (((Class.cv (nb056_alpha_dummy_143))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0149 (f : Var) : (nb056_alpha_dummy_146 f) ∈ (((Class.cv (nb056_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0150 : (nb056_alpha_dummy_085) ∈ (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0151 : (nb056_alpha_dummy_085) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cphi (Class.cv (nb056_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0152 (f : Var) : (nb056_alpha_dummy_087 f) ∈ (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0153 (f : Var) : (nb056_alpha_dummy_087 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0154 : (nb056_alpha_dummy_085) ∈ (((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127) (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085)) (Wff.classEq (Class.cv (nb056_alpha_dummy_127)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0155 (f : Var) : (nb056_alpha_dummy_087 f) ∈ (((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f) (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0156 : (nb056_alpha_dummy_128) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_128))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0157 (f : Var) : (nb056_alpha_dummy_130 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0158 : (nb056_alpha_dummy_128) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0159 (f : Var) : (nb056_alpha_dummy_130 f) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0160 : (nb056_alpha_dummy_000) ∈ (((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0161 (f : Var) : f ∈ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0162 : (nb056_alpha_dummy_000) ∈ (((syn_ccom (Class.cv (nb056_alpha_dummy_000)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0163 (f : Var) : f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0164 : (nb056_alpha_dummy_000) ∈ (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0165 : (nb056_alpha_dummy_000) ∈ (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005)) (syn_ccnv (Class.cv (nb056_alpha_dummy_000))) (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb056_support_mem_0166 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0167 (f : Var) : f ∈ (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb056_alpha_dummy_010 f))) (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_009 f)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb056_support_mem_0168 : (nb056_alpha_dummy_000) ∈ (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_085)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0169 (f : Var) : f ∈ (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_087 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0170 : (nb056_alpha_dummy_000) ∈ (((Class.cv (nb056_alpha_dummy_000))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0171 (f : Var) : f ∈ (((Class.cv f)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0172 : (nb056_alpha_dummy_007) ∈ (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0173 : (nb056_alpha_dummy_007) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0174 (f : Var) : (nb056_alpha_dummy_010 f) ∈ (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0175 (f : Var) : (nb056_alpha_dummy_010 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0176 : (nb056_alpha_dummy_007) ∈ (((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0177 (f : Var) : (nb056_alpha_dummy_010 f) ∈ (((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0178 : (nb056_alpha_dummy_164) ∈ (((Class.cv (nb056_alpha_dummy_164))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0179 (f : Var) : (nb056_alpha_dummy_166 f) ∈ (((Class.cv (nb056_alpha_dummy_166 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0180 : (nb056_alpha_dummy_171) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_171)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_171)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_171))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0181 (f : Var) : (nb056_alpha_dummy_173 f) ∈ (((Wff.classMem (Class.cv (nb056_alpha_dummy_173 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb056_alpha_dummy_173 f)) (syn_c1c))).fv ∪ ((Class.cv (nb056_alpha_dummy_173 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0182 : (nb056_alpha_dummy_171) ∈ (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0183 (f : Var) : (nb056_alpha_dummy_173 f) ∈ (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0184 : (nb056_alpha_dummy_178) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0185 (f : Var) : (nb056_alpha_dummy_181 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0186 : (nb056_alpha_dummy_178) ∈ (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0187 (f : Var) : (nb056_alpha_dummy_181 f) ∈ (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0188 : (nb056_alpha_dummy_179) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0189 (f : Var) : (nb056_alpha_dummy_182 f) ∈ (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪ ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0190 : (nb056_alpha_dummy_179) ∈ (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0191 (f : Var) : (nb056_alpha_dummy_182 f) ∈ (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0192 : (nb056_alpha_dummy_178) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0193 (f : Var) : (nb056_alpha_dummy_181 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0194 : (nb056_alpha_dummy_178) ∈ (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_178))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0195 (f : Var) : (nb056_alpha_dummy_181 f) ∈ (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_181 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0196 : (nb056_alpha_dummy_179) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0197 (f : Var) : (nb056_alpha_dummy_182 f) ∈ (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪ ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0198 : (nb056_alpha_dummy_179) ∈ (((Class.cv (nb056_alpha_dummy_179))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0199 (f : Var) : (nb056_alpha_dummy_182 f) ∈ (((Class.cv (nb056_alpha_dummy_182 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0200 : (nb056_alpha_dummy_006) ∈ (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0201 : (nb056_alpha_dummy_006) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0202 (f : Var) : (nb056_alpha_dummy_009 f) ∈ (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0203 (f : Var) : (nb056_alpha_dummy_009 f) ∈ (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0204 : (nb056_alpha_dummy_006) ∈ (((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163) (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0205 (f : Var) : (nb056_alpha_dummy_009 f) ∈ (((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f) (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0206 : (nb056_alpha_dummy_164) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_164))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0207 (f : Var) : (nb056_alpha_dummy_166 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0208 : (nb056_alpha_dummy_164) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0209 (f : Var) : (nb056_alpha_dummy_166 f) ∈ (((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv ∪ ((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_compact_fv_empty_0000 : (nb056_alpha_dummy_029) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0000 : (nb056_alpha_dummy_029) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_029, fv_syn_c1c] using (nb056_compact_fv_empty_0000)

theorem nb056_compact_fv_empty_0001 (f : Var) : (nb056_alpha_dummy_032 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0001 (f : Var) : (nb056_alpha_dummy_032 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_032, fv_syn_c1c] using (nb056_compact_fv_empty_0001 f)

theorem nb056_compact_fv_empty_0002 : (nb056_alpha_dummy_028) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0002 : (nb056_alpha_dummy_028) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_028, fv_syn_c1c] using (nb056_compact_fv_empty_0002)

theorem nb056_compact_fv_empty_0003 (f : Var) : (nb056_alpha_dummy_031 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0003 (f : Var) : (nb056_alpha_dummy_031 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_031, fv_syn_c1c] using (nb056_compact_fv_empty_0003 f)

theorem nb056_compact_fv_empty_0004 : (nb056_alpha_dummy_027) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0004 : (nb056_alpha_dummy_027) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_027, fv_syn_c1c] using (nb056_compact_fv_empty_0004)

theorem nb056_compact_fv_empty_0005 (f : Var) : (nb056_alpha_dummy_030 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0005 (f : Var) : (nb056_alpha_dummy_030 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_030, fv_syn_c1c] using (nb056_compact_fv_empty_0005 f)

theorem nb056_compact_fv_empty_0006 : (nb056_alpha_dummy_025) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0006 : (nb056_alpha_dummy_025) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_025, fv_syn_c1c] using (nb056_compact_fv_empty_0006)

theorem nb056_compact_fv_empty_0007 (f : Var) : (nb056_alpha_dummy_026 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0007 (f : Var) : (nb056_alpha_dummy_026 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_026, fv_syn_c1c] using (nb056_compact_fv_empty_0007 f)

theorem nb056_compact_fv_empty_0008 : (nb056_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0008 : (nb056_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_021, fv_syn_c1c] using (nb056_compact_fv_empty_0008)

theorem nb056_compact_fv_empty_0009 (f : Var) : (nb056_alpha_dummy_023 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0009 (f : Var) : (nb056_alpha_dummy_023 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_023, fv_syn_c1c] using (nb056_compact_fv_empty_0009 f)

theorem nb056_compact_fv_empty_0010 : (nb056_alpha_dummy_022) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0010 : (nb056_alpha_dummy_022) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_022, fv_syn_c1c] using (nb056_compact_fv_empty_0010)

theorem nb056_compact_fv_empty_0011 (f : Var) : (nb056_alpha_dummy_024 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0011 (f : Var) : (nb056_alpha_dummy_024 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_024, fv_syn_c1c] using (nb056_compact_fv_empty_0011 f)

theorem nb056_compact_fv_empty_0012 : (nb056_alpha_dummy_014) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0012 : (nb056_alpha_dummy_014) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_014, fv_syn_c1c] using (nb056_compact_fv_empty_0012)

theorem nb056_compact_fv_empty_0013 (f : Var) : (nb056_alpha_dummy_016 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0013 (f : Var) : (nb056_alpha_dummy_016 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_016, fv_syn_c1c] using (nb056_compact_fv_empty_0013 f)

theorem nb056_compact_fv_empty_0014 : (nb056_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0014 : (nb056_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_013, fv_syn_c1c] using (nb056_compact_fv_empty_0014)

theorem nb056_compact_fv_empty_0015 (f : Var) : (nb056_alpha_dummy_015 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0015 (f : Var) : (nb056_alpha_dummy_015 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_015, fv_syn_c1c] using (nb056_compact_fv_empty_0015 f)

theorem nb056_compact_fv_empty_0016 : (nb056_alpha_dummy_019) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0016 : (nb056_alpha_dummy_019) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_019, fv_syn_c1c] using (nb056_compact_fv_empty_0016)

theorem nb056_compact_fv_empty_0017 (f : Var) : (nb056_alpha_dummy_020 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0017 (f : Var) : (nb056_alpha_dummy_020 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_020, fv_syn_c1c] using (nb056_compact_fv_empty_0017 f)

theorem nb056_compact_fv_empty_0018 : (nb056_alpha_dummy_017) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0018 : (nb056_alpha_dummy_017) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_017, fv_syn_c1c] using (nb056_compact_fv_empty_0018)

theorem nb056_compact_fv_empty_0019 (f : Var) : (nb056_alpha_dummy_018 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0019 (f : Var) : (nb056_alpha_dummy_018 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_018, fv_syn_c1c] using (nb056_compact_fv_empty_0019 f)

theorem nb056_compact_fv_empty_0020 : (nb056_alpha_dummy_006) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0020 : (nb056_alpha_dummy_006) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_006, fv_syn_c1c] using (nb056_compact_fv_empty_0020)

theorem nb056_compact_fv_empty_0021 (f : Var) : (nb056_alpha_dummy_009 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0021 (f : Var) : (nb056_alpha_dummy_009 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_009, fv_syn_c1c] using (nb056_compact_fv_empty_0021 f)

theorem nb056_compact_fv_empty_0022 : (nb056_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0022 : (nb056_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_005, fv_syn_c1c] using (nb056_compact_fv_empty_0022)

theorem nb056_compact_fv_empty_0023 (f : Var) : (nb056_alpha_dummy_008 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0023 (f : Var) : (nb056_alpha_dummy_008 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_008, fv_syn_c1c] using (nb056_compact_fv_empty_0023 f)

theorem nb056_compact_fv_empty_0024 : (nb056_alpha_dummy_011) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0024 : (nb056_alpha_dummy_011) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_011, fv_syn_c1c] using (nb056_compact_fv_empty_0024)

theorem nb056_compact_fv_empty_0025 (f : Var) : (nb056_alpha_dummy_012 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0025 (f : Var) : (nb056_alpha_dummy_012 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_012, fv_syn_c1c] using (nb056_compact_fv_empty_0025 f)

theorem nb056_compact_fv_empty_0026 : (nb056_alpha_dummy_003) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0026 : (nb056_alpha_dummy_003) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_003, fv_syn_c1c] using (nb056_compact_fv_empty_0026)

theorem nb056_compact_fv_empty_0027 (f : Var) : (nb056_alpha_dummy_004 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0027 (f : Var) : (nb056_alpha_dummy_004 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_004, fv_syn_c1c] using (nb056_compact_fv_empty_0027 f)

theorem nb056_compact_fv_empty_0028 : (nb056_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0028 : (nb056_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_001, fv_syn_c1c] using (nb056_compact_fv_empty_0028)

theorem nb056_compact_fv_empty_0029 (f : Var) : (nb056_alpha_dummy_002 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0029 (f : Var) : (nb056_alpha_dummy_002 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_002, fv_syn_c1c] using (nb056_compact_fv_empty_0029 f)

theorem nb056_compact_fv_empty_0030 : (nb056_alpha_dummy_000) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0030 : (nb056_alpha_dummy_000) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_000, fv_syn_c1c] using (nb056_compact_fv_empty_0030)

theorem nb056_compact_fv_empty_0031 (f : Var) : f ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0031 (f : Var) : f ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb056_compact_fv_empty_0031 f)

theorem nb056_compact_envfresh_0000 (f : Var) : TEnvFresh [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_029) (nb056_alpha_dummy_032 f) (nb056_wpp_notmem_0000) (nb056_wpp_notmem_0001 f) (TEnvFresh.consFresh (nb056_alpha_dummy_028) (nb056_alpha_dummy_031 f) (nb056_wpp_notmem_0002) (nb056_wpp_notmem_0003 f) (TEnvFresh.consFresh (nb056_alpha_dummy_027) (nb056_alpha_dummy_030 f) (nb056_wpp_notmem_0004) (nb056_wpp_notmem_0005 f) (TEnvFresh.consFresh (nb056_alpha_dummy_025) (nb056_alpha_dummy_026 f) (nb056_wpp_notmem_0006) (nb056_wpp_notmem_0007 f) (TEnvFresh.consFresh (nb056_alpha_dummy_021) (nb056_alpha_dummy_023 f) (nb056_wpp_notmem_0008) (nb056_wpp_notmem_0009 f) (TEnvFresh.consFresh (nb056_alpha_dummy_022) (nb056_alpha_dummy_024 f) (nb056_wpp_notmem_0010) (nb056_wpp_notmem_0011 f) (TEnvFresh.consFresh (nb056_alpha_dummy_014) (nb056_alpha_dummy_016 f) (nb056_wpp_notmem_0012) (nb056_wpp_notmem_0013 f) (TEnvFresh.consFresh (nb056_alpha_dummy_013) (nb056_alpha_dummy_015 f) (nb056_wpp_notmem_0014) (nb056_wpp_notmem_0015 f) (TEnvFresh.consFresh (nb056_alpha_dummy_019) (nb056_alpha_dummy_020 f) (nb056_wpp_notmem_0016) (nb056_wpp_notmem_0017 f) (TEnvFresh.consFresh (nb056_alpha_dummy_017) (nb056_alpha_dummy_018 f) (nb056_wpp_notmem_0018) (nb056_wpp_notmem_0019 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0020) (nb056_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0022) (nb056_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0024) (nb056_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0026) (nb056_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0028) (nb056_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0030) (nb056_wpp_notmem_0031 f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb056_wpp_refl_0000 (f : Var) : TReflOn [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0000 f)

theorem nb056_wpp_notmem_0032 : (nb056_alpha_dummy_029) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_029, fv_syn_c0] using (nb056_compact_fv_empty_0000)

theorem nb056_wpp_notmem_0033 (f : Var) : (nb056_alpha_dummy_032 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_032, fv_syn_c0] using (nb056_compact_fv_empty_0001 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
