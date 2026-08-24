import NAR4C068C001Part010

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

theorem nb068_support_mem_0215 : (nb068_alpha_dummy_047) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0216 (f : Var) : (nb068_alpha_dummy_050 f) ∈ (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0217 (f : Var) : (nb068_alpha_dummy_050 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0218 : (nb068_alpha_dummy_047) ∈ (((Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cphi (Class.cv (nb068_alpha_dummy_204))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0219 (f : Var) : (nb068_alpha_dummy_050 f) ∈ (((Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0220 : (nb068_alpha_dummy_204) ∈ (((Class.cv (nb068_alpha_dummy_204))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0221 (f : Var) : (nb068_alpha_dummy_206 f) ∈ (((Class.cv (nb068_alpha_dummy_206 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0222 : (nb068_alpha_dummy_211) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_211)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_211)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_211))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0223 (f : Var) : (nb068_alpha_dummy_213 f) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_213 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_213 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_213 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0224 : (nb068_alpha_dummy_211) ∈ (((Class.cv (nb068_alpha_dummy_211))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0225 (f : Var) : (nb068_alpha_dummy_213 f) ∈ (((Class.cv (nb068_alpha_dummy_213 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0226 : (nb068_alpha_dummy_218) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0227 (f : Var) : (nb068_alpha_dummy_221 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0228 : (nb068_alpha_dummy_218) ∈ (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0229 (f : Var) : (nb068_alpha_dummy_221 f) ∈ (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0230 : (nb068_alpha_dummy_219) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_218)) (Class.cv (nb068_alpha_dummy_219)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0231 (f : Var) : (nb068_alpha_dummy_222 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_221 f)) (Class.cv (nb068_alpha_dummy_222 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0232 : (nb068_alpha_dummy_219) ∈ (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0233 (f : Var) : (nb068_alpha_dummy_222 f) ∈ (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0234 : (nb068_alpha_dummy_218) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0235 (f : Var) : (nb068_alpha_dummy_221 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0236 : (nb068_alpha_dummy_218) ∈ (((Class.cv (nb068_alpha_dummy_218))).fv ∪ ((Class.cv (nb068_alpha_dummy_218))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0237 (f : Var) : (nb068_alpha_dummy_221 f) ∈ (((Class.cv (nb068_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_221 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0238 : (nb068_alpha_dummy_219) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0239 (f : Var) : (nb068_alpha_dummy_222 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0240 : (nb068_alpha_dummy_219) ∈ (((Class.cv (nb068_alpha_dummy_219))).fv ∪ ((Class.cv (nb068_alpha_dummy_219))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0241 (f : Var) : (nb068_alpha_dummy_222 f) ∈ (((Class.cv (nb068_alpha_dummy_222 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_222 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0242 : (nb068_alpha_dummy_046) ∈ (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0243 : (nb068_alpha_dummy_046) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0244 (f : Var) : (nb068_alpha_dummy_049 f) ∈ (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0245 (f : Var) : (nb068_alpha_dummy_049 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0246 : (nb068_alpha_dummy_046) ∈ (((Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0247 (f : Var) : (nb068_alpha_dummy_049 f) ∈ (((Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0248 : (nb068_alpha_dummy_204) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_204))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0249 (f : Var) : (nb068_alpha_dummy_206 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0250 : (nb068_alpha_dummy_204) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_204)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0251 (f : Var) : (nb068_alpha_dummy_206 f) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0252 : (nb068_alpha_dummy_240) ∈ (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0253 : (nb068_alpha_dummy_240) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0254 (f : Var) : (nb068_alpha_dummy_242 f) ∈ (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0255 (f : Var) : (nb068_alpha_dummy_242 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0256 : (nb068_alpha_dummy_240) ∈ (((Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0257 (f : Var) : (nb068_alpha_dummy_242 f) ∈ (((Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0258 : (nb068_alpha_dummy_244) ∈ (((Class.cv (nb068_alpha_dummy_244))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0259 (f : Var) : (nb068_alpha_dummy_246 f) ∈ (((Class.cv (nb068_alpha_dummy_246 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0260 : (nb068_alpha_dummy_251) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_251)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_251)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_251))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0261 (f : Var) : (nb068_alpha_dummy_253 f) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_253 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_253 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_253 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0262 : (nb068_alpha_dummy_251) ∈ (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0263 (f : Var) : (nb068_alpha_dummy_253 f) ∈ (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0264 : (nb068_alpha_dummy_258) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0265 (f : Var) : (nb068_alpha_dummy_261 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0266 : (nb068_alpha_dummy_258) ∈ (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0267 (f : Var) : (nb068_alpha_dummy_261 f) ∈ (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0268 : (nb068_alpha_dummy_259) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0269 (f : Var) : (nb068_alpha_dummy_262 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0270 : (nb068_alpha_dummy_259) ∈ (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0271 (f : Var) : (nb068_alpha_dummy_262 f) ∈ (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0272 : (nb068_alpha_dummy_258) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0273 (f : Var) : (nb068_alpha_dummy_261 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0274 : (nb068_alpha_dummy_258) ∈ (((Class.cv (nb068_alpha_dummy_258))).fv ∪ ((Class.cv (nb068_alpha_dummy_258))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0275 (f : Var) : (nb068_alpha_dummy_261 f) ∈ (((Class.cv (nb068_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_261 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0276 : (nb068_alpha_dummy_259) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0277 (f : Var) : (nb068_alpha_dummy_262 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0278 : (nb068_alpha_dummy_259) ∈ (((Class.cv (nb068_alpha_dummy_259))).fv ∪ ((Class.cv (nb068_alpha_dummy_259))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0279 (f : Var) : (nb068_alpha_dummy_262 f) ∈ (((Class.cv (nb068_alpha_dummy_262 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_262 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0280 : (nb068_alpha_dummy_239) ∈ (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0281 : (nb068_alpha_dummy_239) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0282 (f : Var) : (nb068_alpha_dummy_241 f) ∈ (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0283 (f : Var) : (nb068_alpha_dummy_241 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0284 : (nb068_alpha_dummy_239) ∈ (((Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0285 (f : Var) : (nb068_alpha_dummy_241 f) ∈ (((Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0286 : (nb068_alpha_dummy_244) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_244))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0287 (f : Var) : (nb068_alpha_dummy_246 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0288 : (nb068_alpha_dummy_244) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_244)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0289 (f : Var) : (nb068_alpha_dummy_246 f) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0290 : (nb068_alpha_dummy_000) ∈ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0291 (f : Var) : f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0292 : (nb068_alpha_dummy_284) ∈ (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0293 : (nb068_alpha_dummy_284) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0294 (f : Var) : (nb068_alpha_dummy_286 f) ∈ (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0295 (f : Var) : (nb068_alpha_dummy_286 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0296 : (nb068_alpha_dummy_284) ∈ (((Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0297 (f : Var) : (nb068_alpha_dummy_286 f) ∈ (((Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0298 : (nb068_alpha_dummy_288) ∈ (((Class.cv (nb068_alpha_dummy_288))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0299 (f : Var) : (nb068_alpha_dummy_290 f) ∈ (((Class.cv (nb068_alpha_dummy_290 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0300 : (nb068_alpha_dummy_295) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_295))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0301 (f : Var) : (nb068_alpha_dummy_297 f) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_297 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0302 : (nb068_alpha_dummy_295) ∈ (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0303 (f : Var) : (nb068_alpha_dummy_297 f) ∈ (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0304 : (nb068_alpha_dummy_302) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0305 (f : Var) : (nb068_alpha_dummy_305 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0306 : (nb068_alpha_dummy_302) ∈ (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0307 (f : Var) : (nb068_alpha_dummy_305 f) ∈ (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0308 : (nb068_alpha_dummy_303) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0309 (f : Var) : (nb068_alpha_dummy_306 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0310 : (nb068_alpha_dummy_303) ∈ (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0311 (f : Var) : (nb068_alpha_dummy_306 f) ∈ (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0312 : (nb068_alpha_dummy_302) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0313 (f : Var) : (nb068_alpha_dummy_305 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0314 : (nb068_alpha_dummy_302) ∈ (((Class.cv (nb068_alpha_dummy_302))).fv ∪ ((Class.cv (nb068_alpha_dummy_302))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0315 (f : Var) : (nb068_alpha_dummy_305 f) ∈ (((Class.cv (nb068_alpha_dummy_305 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_305 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0316 : (nb068_alpha_dummy_303) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0317 (f : Var) : (nb068_alpha_dummy_306 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0318 : (nb068_alpha_dummy_303) ∈ (((Class.cv (nb068_alpha_dummy_303))).fv ∪ ((Class.cv (nb068_alpha_dummy_303))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0319 (f : Var) : (nb068_alpha_dummy_306 f) ∈ (((Class.cv (nb068_alpha_dummy_306 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_306 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0320 : (nb068_alpha_dummy_283) ∈ (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0321 : (nb068_alpha_dummy_283) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0322 (f : Var) : (nb068_alpha_dummy_285 f) ∈ (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0323 (f : Var) : (nb068_alpha_dummy_285 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0324 : (nb068_alpha_dummy_283) ∈ (((Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0325 (f : Var) : (nb068_alpha_dummy_285 f) ∈ (((Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0326 : (nb068_alpha_dummy_288) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_288))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0327 (f : Var) : (nb068_alpha_dummy_290 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0328 : (nb068_alpha_dummy_288) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_288)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0329 (f : Var) : (nb068_alpha_dummy_290 f) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0330 : (nb068_alpha_dummy_000) ∈ (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0331 (y : Var) (f : Var) : f ∈ (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0332 : (nb068_alpha_dummy_000) ∈ (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0333 (y : Var) (f : Var) : f ∈ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0334 : (nb068_alpha_dummy_000) ∈ (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0335 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0336 : (nb068_alpha_dummy_002) ∈ (((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_002)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0337 (y : Var) (f : Var) : y ∈ (((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv f)) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0338 : (nb068_alpha_dummy_002) ∈ (((syn_crn (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0339 (y : Var) (f : Var) : y ∈ (((syn_crn (Class.cv f))).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0340 : (nb068_alpha_dummy_327) ∈ (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327)) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_328)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0341 (f : Var) : (nb068_alpha_dummy_330 f) ∈ (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_330 f)) (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_331 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0342 : (nb068_alpha_dummy_328) ∈ (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327)) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_328)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0343 (f : Var) : (nb068_alpha_dummy_331 f) ∈ (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_330 f)) (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_331 f)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0344 : (nb068_alpha_dummy_327) ∈ (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0345 : (nb068_alpha_dummy_327) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cphi (Class.cv (nb068_alpha_dummy_336)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0346 (f : Var) : (nb068_alpha_dummy_330 f) ∈ (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0347 (f : Var) : (nb068_alpha_dummy_330 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0348 : (nb068_alpha_dummy_327) ∈ (((Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cphi (Class.cv (nb068_alpha_dummy_336))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0349 (f : Var) : (nb068_alpha_dummy_330 f) ∈ (((Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0350 : (nb068_alpha_dummy_336) ∈ (((Class.cv (nb068_alpha_dummy_336))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0351 (f : Var) : (nb068_alpha_dummy_338 f) ∈ (((Class.cv (nb068_alpha_dummy_338 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0352 : (nb068_alpha_dummy_343) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_343))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0353 (f : Var) : (nb068_alpha_dummy_345 f) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_345 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0354 : (nb068_alpha_dummy_343) ∈ (((Class.cv (nb068_alpha_dummy_343))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0355 (f : Var) : (nb068_alpha_dummy_345 f) ∈ (((Class.cv (nb068_alpha_dummy_345 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
