import NAR4C078C001Part022

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

theorem nb078_support_mem_0171 (f : Var) : f ∈ (((Class.cv f)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0172 : (nb078_alpha_dummy_011) ∈ (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0173 : (nb078_alpha_dummy_011) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0174 (f : Var) : (nb078_alpha_dummy_014 f) ∈ (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0175 (f : Var) : (nb078_alpha_dummy_014 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0176 : (nb078_alpha_dummy_011) ∈ (((Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0177 (f : Var) : (nb078_alpha_dummy_014 f) ∈ (((Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0178 : (nb078_alpha_dummy_168) ∈ (((Class.cv (nb078_alpha_dummy_168))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0179 (f : Var) : (nb078_alpha_dummy_170 f) ∈ (((Class.cv (nb078_alpha_dummy_170 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0180 : (nb078_alpha_dummy_175) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_175)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_175)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_175))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0181 (f : Var) : (nb078_alpha_dummy_177 f) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_177 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_177 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_177 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0182 : (nb078_alpha_dummy_175) ∈ (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0183 (f : Var) : (nb078_alpha_dummy_177 f) ∈ (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0184 : (nb078_alpha_dummy_182) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0185 (f : Var) : (nb078_alpha_dummy_185 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0186 : (nb078_alpha_dummy_182) ∈ (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0187 (f : Var) : (nb078_alpha_dummy_185 f) ∈ (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0188 : (nb078_alpha_dummy_183) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0189 (f : Var) : (nb078_alpha_dummy_186 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f)) (Class.cv (nb078_alpha_dummy_186 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0190 : (nb078_alpha_dummy_183) ∈ (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0191 (f : Var) : (nb078_alpha_dummy_186 f) ∈ (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0192 : (nb078_alpha_dummy_182) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_182)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_183)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0193 (f : Var) : (nb078_alpha_dummy_185 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_185 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_186 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0194 : (nb078_alpha_dummy_182) ∈ (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_182))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0195 (f : Var) : (nb078_alpha_dummy_185 f) ∈ (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_185 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0196 : (nb078_alpha_dummy_183) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_182)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_183)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0197 (f : Var) : (nb078_alpha_dummy_186 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_185 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_186 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0198 : (nb078_alpha_dummy_183) ∈ (((Class.cv (nb078_alpha_dummy_183))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0199 (f : Var) : (nb078_alpha_dummy_186 f) ∈ (((Class.cv (nb078_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0200 : (nb078_alpha_dummy_010) ∈ (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0201 : (nb078_alpha_dummy_010) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0202 (f : Var) : (nb078_alpha_dummy_013 f) ∈ (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0203 (f : Var) : (nb078_alpha_dummy_013 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0204 : (nb078_alpha_dummy_010) ∈ (((Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_167) (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010)) (Wff.classEq (Class.cv (nb078_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0205 (f : Var) : (nb078_alpha_dummy_013 f) ∈ (((Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_169 f) (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0206 : (nb078_alpha_dummy_168) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0207 (f : Var) : (nb078_alpha_dummy_170 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0208 : (nb078_alpha_dummy_168) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0209 (f : Var) : (nb078_alpha_dummy_170 f) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0210 : (nb078_alpha_dummy_204) ∈ (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0211 : (nb078_alpha_dummy_204) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cphi (Class.cv (nb078_alpha_dummy_208)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0212 (f : Var) : (nb078_alpha_dummy_206 f) ∈ (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0213 (f : Var) : (nb078_alpha_dummy_206 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0214 : (nb078_alpha_dummy_204) ∈ (((Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0215 (f : Var) : (nb078_alpha_dummy_206 f) ∈ (((Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0216 : (nb078_alpha_dummy_208) ∈ (((Class.cv (nb078_alpha_dummy_208))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0217 (f : Var) : (nb078_alpha_dummy_210 f) ∈ (((Class.cv (nb078_alpha_dummy_210 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0218 : (nb078_alpha_dummy_215) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_215)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_215)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_215))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0219 (f : Var) : (nb078_alpha_dummy_217 f) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_217 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_217 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_217 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0220 : (nb078_alpha_dummy_215) ∈ (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0221 (f : Var) : (nb078_alpha_dummy_217 f) ∈ (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0222 : (nb078_alpha_dummy_222) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0223 (f : Var) : (nb078_alpha_dummy_225 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0224 : (nb078_alpha_dummy_222) ∈ (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0225 (f : Var) : (nb078_alpha_dummy_225 f) ∈ (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0226 : (nb078_alpha_dummy_223) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0227 (f : Var) : (nb078_alpha_dummy_226 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f)) (Class.cv (nb078_alpha_dummy_226 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0228 : (nb078_alpha_dummy_223) ∈ (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0229 (f : Var) : (nb078_alpha_dummy_226 f) ∈ (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0230 : (nb078_alpha_dummy_222) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_222)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_223)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0231 (f : Var) : (nb078_alpha_dummy_225 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_225 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_226 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0232 : (nb078_alpha_dummy_222) ∈ (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_222))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0233 (f : Var) : (nb078_alpha_dummy_225 f) ∈ (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_225 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0234 : (nb078_alpha_dummy_223) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_222)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_223)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0235 (f : Var) : (nb078_alpha_dummy_226 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_225 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_226 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0236 : (nb078_alpha_dummy_223) ∈ (((Class.cv (nb078_alpha_dummy_223))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0237 (f : Var) : (nb078_alpha_dummy_226 f) ∈ (((Class.cv (nb078_alpha_dummy_226 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0238 : (nb078_alpha_dummy_203) ∈ (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0239 : (nb078_alpha_dummy_203) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cphi (Class.cv (nb078_alpha_dummy_208)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0240 (f : Var) : (nb078_alpha_dummy_205 f) ∈ (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0241 (f : Var) : (nb078_alpha_dummy_205 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0242 : (nb078_alpha_dummy_203) ∈ (((Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_207) (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203)) (Wff.classEq (Class.cv (nb078_alpha_dummy_207)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0243 (f : Var) : (nb078_alpha_dummy_205 f) ∈ (((Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_209 f) (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0244 : (nb078_alpha_dummy_208) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_208))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0245 (f : Var) : (nb078_alpha_dummy_210 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0246 : (nb078_alpha_dummy_208) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0247 (f : Var) : (nb078_alpha_dummy_210 f) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0248 : (nb078_alpha_dummy_000) ∈ (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0249 (f : Var) : f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0250 : (nb078_alpha_dummy_244) ∈ (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0251 : (nb078_alpha_dummy_244) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cphi (Class.cv (nb078_alpha_dummy_248)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0252 (f : Var) : (nb078_alpha_dummy_246 f) ∈ (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0253 (f : Var) : (nb078_alpha_dummy_246 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0254 : (nb078_alpha_dummy_244) ∈ (((Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0255 (f : Var) : (nb078_alpha_dummy_246 f) ∈ (((Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0256 : (nb078_alpha_dummy_248) ∈ (((Class.cv (nb078_alpha_dummy_248))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0257 (f : Var) : (nb078_alpha_dummy_250 f) ∈ (((Class.cv (nb078_alpha_dummy_250 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0258 : (nb078_alpha_dummy_255) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_255)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_255)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_255))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0259 (f : Var) : (nb078_alpha_dummy_257 f) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_257 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_257 f)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_257 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0260 : (nb078_alpha_dummy_255) ∈ (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0261 (f : Var) : (nb078_alpha_dummy_257 f) ∈ (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0262 : (nb078_alpha_dummy_262) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0263 (f : Var) : (nb078_alpha_dummy_265 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0264 : (nb078_alpha_dummy_262) ∈ (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0265 (f : Var) : (nb078_alpha_dummy_265 f) ∈ (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0266 : (nb078_alpha_dummy_263) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0267 (f : Var) : (nb078_alpha_dummy_266 f) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f)) (Class.cv (nb078_alpha_dummy_266 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0268 : (nb078_alpha_dummy_263) ∈ (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0269 (f : Var) : (nb078_alpha_dummy_266 f) ∈ (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0270 : (nb078_alpha_dummy_262) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_262)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_263)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0271 (f : Var) : (nb078_alpha_dummy_265 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_265 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_266 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0272 : (nb078_alpha_dummy_262) ∈ (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_262))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0273 (f : Var) : (nb078_alpha_dummy_265 f) ∈ (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_265 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0274 : (nb078_alpha_dummy_263) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_262)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_263)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0275 (f : Var) : (nb078_alpha_dummy_266 f) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_265 f)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_266 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0276 : (nb078_alpha_dummy_263) ∈ (((Class.cv (nb078_alpha_dummy_263))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0277 (f : Var) : (nb078_alpha_dummy_266 f) ∈ (((Class.cv (nb078_alpha_dummy_266 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0278 : (nb078_alpha_dummy_243) ∈ (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0279 : (nb078_alpha_dummy_243) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cphi (Class.cv (nb078_alpha_dummy_248)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0280 (f : Var) : (nb078_alpha_dummy_245 f) ∈ (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0281 (f : Var) : (nb078_alpha_dummy_245 f) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0282 : (nb078_alpha_dummy_243) ∈ (((Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_247) (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243)) (Wff.classEq (Class.cv (nb078_alpha_dummy_247)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0283 (f : Var) : (nb078_alpha_dummy_245 f) ∈ (((Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_249 f) (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f)) (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0284 : (nb078_alpha_dummy_248) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_248))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0285 (f : Var) : (nb078_alpha_dummy_250 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0286 : (nb078_alpha_dummy_248) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0287 (f : Var) : (nb078_alpha_dummy_250 f) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0288 : (nb078_alpha_dummy_000) ∈ (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0289 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0290 : (nb078_alpha_dummy_287) ∈ (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0291 (g : Var) : (nb078_alpha_dummy_290 g) ∈ (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_292 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_291 g)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0292 : (nb078_alpha_dummy_288) ∈ (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0293 (g : Var) : (nb078_alpha_dummy_291 g) ∈ (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_292 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_291 g)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0294 : (nb078_alpha_dummy_287) ∈ (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0295 : (nb078_alpha_dummy_287) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cphi (Class.cv (nb078_alpha_dummy_296)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0296 (g : Var) : (nb078_alpha_dummy_290 g) ∈ (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0297 (g : Var) : (nb078_alpha_dummy_290 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0298 : (nb078_alpha_dummy_287) ∈ (((Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_295) (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287)) (Wff.classEq (Class.cv (nb078_alpha_dummy_295)) (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0299 (g : Var) : (nb078_alpha_dummy_290 g) ∈ (((Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_297 g) (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0300 : (nb078_alpha_dummy_296) ∈ (((Class.cv (nb078_alpha_dummy_296))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0301 (g : Var) : (nb078_alpha_dummy_298 g) ∈ (((Class.cv (nb078_alpha_dummy_298 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0302 : (nb078_alpha_dummy_303) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_303)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_303)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_303))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0303 (g : Var) : (nb078_alpha_dummy_305 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_305 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_305 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_305 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0304 : (nb078_alpha_dummy_303) ∈ (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0305 (g : Var) : (nb078_alpha_dummy_305 g) ∈ (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0306 : (nb078_alpha_dummy_310) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0307 (g : Var) : (nb078_alpha_dummy_313 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0308 : (nb078_alpha_dummy_310) ∈ (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0309 (g : Var) : (nb078_alpha_dummy_313 g) ∈ (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0310 : (nb078_alpha_dummy_311) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0311 (g : Var) : (nb078_alpha_dummy_314 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g)) (Class.cv (nb078_alpha_dummy_314 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0312 : (nb078_alpha_dummy_311) ∈ (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
