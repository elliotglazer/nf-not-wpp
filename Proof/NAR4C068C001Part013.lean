import NAR4C068C001Part012

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

theorem nb068_support_mem_0498 : (nb068_alpha_dummy_450) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_450)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0499 (f : Var) : (nb068_alpha_dummy_452 f) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0500 : (nb068_alpha_dummy_000) ∈ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0501 (f : Var) : f ∈ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0502 : (nb068_alpha_dummy_000) ∈ (((syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0503 (f : Var) : f ∈ (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0504 : (nb068_alpha_dummy_000) ∈ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0505 : (nb068_alpha_dummy_000) ∈ (({(nb068_alpha_dummy_327)} : Finset Var) ∪ ({(nb068_alpha_dummy_328)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_329) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_327)) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))) (Class.cv (nb068_alpha_dummy_329))) (syn_wbr (Class.cv (nb068_alpha_dummy_329)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_328)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0504) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0506 (f : Var) : f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0507 (f : Var) : f ∈ (({(nb068_alpha_dummy_330 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_331 f)} : Finset Var) ∪ ((syn_wex (nb068_alpha_dummy_332 f) (syn_wa (syn_wbr (Class.cv (nb068_alpha_dummy_330 f)) (syn_ccnv (syn_ccnv (Class.cv f))) (Class.cv (nb068_alpha_dummy_332 f))) (syn_wbr (Class.cv (nb068_alpha_dummy_332 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_331 f)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0506 f) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0508 : (nb068_alpha_dummy_000) ∈ (({(nb068_alpha_dummy_407)} : Finset Var) ∪ ({(nb068_alpha_dummy_408)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_408)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (Class.cv (nb068_alpha_dummy_407)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0509 (f : Var) : f ∈ (({(nb068_alpha_dummy_409 f)} : Finset Var) ∪ ({(nb068_alpha_dummy_410 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb068_alpha_dummy_410 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb068_alpha_dummy_409 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0510 : (nb068_alpha_dummy_000) ∈ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) := by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0511 (f : Var) : f ∈ (((syn_ccnv (Class.cv f))).fv) := by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0512 : (nb068_alpha_dummy_329) ∈ (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0513 : (nb068_alpha_dummy_329) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0514 (f : Var) : (nb068_alpha_dummy_332 f) ∈ (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0515 (f : Var) : (nb068_alpha_dummy_332 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0516 : (nb068_alpha_dummy_329) ∈ (((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0512) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0517 (f : Var) : (nb068_alpha_dummy_332 f) ∈ (((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0514 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0518 : (nb068_alpha_dummy_486) ∈ (((Class.cv (nb068_alpha_dummy_486))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0519 (f : Var) : (nb068_alpha_dummy_488 f) ∈ (((Class.cv (nb068_alpha_dummy_488 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0520 : (nb068_alpha_dummy_493) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_493)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_493)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_493))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0521 (f : Var) : (nb068_alpha_dummy_495 f) ∈ (((Wff.classMem (Class.cv (nb068_alpha_dummy_495 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb068_alpha_dummy_495 f)) (syn_c1c))).fv ∪ ((Class.cv (nb068_alpha_dummy_495 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0522 : (nb068_alpha_dummy_493) ∈ (((Class.cv (nb068_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0523 (f : Var) : (nb068_alpha_dummy_495 f) ∈ (((Class.cv (nb068_alpha_dummy_495 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0524 : (nb068_alpha_dummy_500) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0525 (f : Var) : (nb068_alpha_dummy_503 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_503 f)) (Class.cv (nb068_alpha_dummy_504 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_503 f)) (Class.cv (nb068_alpha_dummy_504 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0526 : (nb068_alpha_dummy_500) ∈ (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0527 (f : Var) : (nb068_alpha_dummy_503 f) ∈ (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0528 : (nb068_alpha_dummy_501) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_500)) (Class.cv (nb068_alpha_dummy_501)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0529 (f : Var) : (nb068_alpha_dummy_504 f) ∈ (((syn_cnin (Class.cv (nb068_alpha_dummy_503 f)) (Class.cv (nb068_alpha_dummy_504 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_503 f)) (Class.cv (nb068_alpha_dummy_504 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0530 : (nb068_alpha_dummy_501) ∈ (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0531 (f : Var) : (nb068_alpha_dummy_504 f) ∈ (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0532 : (nb068_alpha_dummy_500) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_500)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_501)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0533 (f : Var) : (nb068_alpha_dummy_503 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_503 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_504 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0534 : (nb068_alpha_dummy_500) ∈ (((Class.cv (nb068_alpha_dummy_500))).fv ∪ ((Class.cv (nb068_alpha_dummy_500))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0535 (f : Var) : (nb068_alpha_dummy_503 f) ∈ (((Class.cv (nb068_alpha_dummy_503 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_503 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0536 : (nb068_alpha_dummy_501) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_500)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_501)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0537 (f : Var) : (nb068_alpha_dummy_504 f) ∈ (((syn_ccompl (Class.cv (nb068_alpha_dummy_503 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_504 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0538 : (nb068_alpha_dummy_501) ∈ (((Class.cv (nb068_alpha_dummy_501))).fv ∪ ((Class.cv (nb068_alpha_dummy_501))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0539 (f : Var) : (nb068_alpha_dummy_504 f) ∈ (((Class.cv (nb068_alpha_dummy_504 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_504 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0540 : (nb068_alpha_dummy_328) ∈ (((Class.cv (nb068_alpha_dummy_329))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0541 : (nb068_alpha_dummy_328) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0542 (f : Var) : (nb068_alpha_dummy_331 f) ∈ (((Class.cv (nb068_alpha_dummy_332 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0543 (f : Var) : (nb068_alpha_dummy_331 f) ∈ (((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0544 : (nb068_alpha_dummy_328) ∈ (((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0540) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0545 (f : Var) : (nb068_alpha_dummy_331 f) ∈ (((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0542 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0546 : (nb068_alpha_dummy_486) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_486))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0547 (f : Var) : (nb068_alpha_dummy_488 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0548 : (nb068_alpha_dummy_486) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_486)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0549 (f : Var) : (nb068_alpha_dummy_488 f) ∈ (((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv ∪ ((syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_compact_fv_empty_0000 : (nb068_alpha_dummy_021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0000 : (nb068_alpha_dummy_021) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_021, fv_syn_c1c] using (nb068_compact_fv_empty_0000)

theorem nb068_compact_fv_empty_0001 (x : Var) (y : Var) : (nb068_alpha_dummy_024 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0001 (x : Var) (y : Var) : (nb068_alpha_dummy_024 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_024, fv_syn_c1c] using (nb068_compact_fv_empty_0001 x y)

theorem nb068_compact_fv_empty_0002 : (nb068_alpha_dummy_020) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0002 : (nb068_alpha_dummy_020) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_020, fv_syn_c1c] using (nb068_compact_fv_empty_0002)

theorem nb068_compact_fv_empty_0003 (x : Var) (y : Var) : (nb068_alpha_dummy_023 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0003 (x : Var) (y : Var) : (nb068_alpha_dummy_023 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_023, fv_syn_c1c] using (nb068_compact_fv_empty_0003 x y)

theorem nb068_compact_fv_empty_0004 : (nb068_alpha_dummy_019) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0004 : (nb068_alpha_dummy_019) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_019, fv_syn_c1c] using (nb068_compact_fv_empty_0004)

theorem nb068_compact_fv_empty_0005 (x : Var) (y : Var) : (nb068_alpha_dummy_022 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0005 (x : Var) (y : Var) : (nb068_alpha_dummy_022 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_022, fv_syn_c1c] using (nb068_compact_fv_empty_0005 x y)

theorem nb068_compact_fv_empty_0006 : (nb068_alpha_dummy_017) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0006 : (nb068_alpha_dummy_017) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_017, fv_syn_c1c] using (nb068_compact_fv_empty_0006)

theorem nb068_compact_fv_empty_0007 (x : Var) (y : Var) : (nb068_alpha_dummy_018 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0007 (x : Var) (y : Var) : (nb068_alpha_dummy_018 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_018, fv_syn_c1c] using (nb068_compact_fv_empty_0007 x y)

theorem nb068_compact_fv_empty_0008 : (nb068_alpha_dummy_013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0008 : (nb068_alpha_dummy_013) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_013, fv_syn_c1c] using (nb068_compact_fv_empty_0008)

theorem nb068_compact_fv_empty_0009 (x : Var) (y : Var) : (nb068_alpha_dummy_015 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0009 (x : Var) (y : Var) : (nb068_alpha_dummy_015 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_015, fv_syn_c1c] using (nb068_compact_fv_empty_0009 x y)

theorem nb068_compact_fv_empty_0010 : (nb068_alpha_dummy_014) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0010 : (nb068_alpha_dummy_014) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_014, fv_syn_c1c] using (nb068_compact_fv_empty_0010)

theorem nb068_compact_fv_empty_0011 (x : Var) (y : Var) : (nb068_alpha_dummy_016 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0011 (x : Var) (y : Var) : (nb068_alpha_dummy_016 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_016, fv_syn_c1c] using (nb068_compact_fv_empty_0011 x y)

theorem nb068_compact_fv_empty_0012 : (nb068_alpha_dummy_006) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0012 : (nb068_alpha_dummy_006) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_006, fv_syn_c1c] using (nb068_compact_fv_empty_0012)

theorem nb068_compact_fv_empty_0013 (x : Var) (y : Var) : (nb068_alpha_dummy_008 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0013 (x : Var) (y : Var) : (nb068_alpha_dummy_008 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_008, fv_syn_c1c] using (nb068_compact_fv_empty_0013 x y)

theorem nb068_compact_fv_empty_0014 : (nb068_alpha_dummy_005) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0014 : (nb068_alpha_dummy_005) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_005, fv_syn_c1c] using (nb068_compact_fv_empty_0014)

theorem nb068_compact_fv_empty_0015 (x : Var) (y : Var) : (nb068_alpha_dummy_007 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0015 (x : Var) (y : Var) : (nb068_alpha_dummy_007 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_007, fv_syn_c1c] using (nb068_compact_fv_empty_0015 x y)

theorem nb068_compact_fv_empty_0016 : (nb068_alpha_dummy_011) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0016 : (nb068_alpha_dummy_011) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_011, fv_syn_c1c] using (nb068_compact_fv_empty_0016)

theorem nb068_compact_fv_empty_0017 (x : Var) (y : Var) : (nb068_alpha_dummy_012 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0017 (x : Var) (y : Var) : (nb068_alpha_dummy_012 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_012, fv_syn_c1c] using (nb068_compact_fv_empty_0017 x y)

theorem nb068_compact_fv_empty_0018 : (nb068_alpha_dummy_009) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0018 : (nb068_alpha_dummy_009) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_009, fv_syn_c1c] using (nb068_compact_fv_empty_0018)

theorem nb068_compact_fv_empty_0019 (x : Var) (y : Var) : (nb068_alpha_dummy_010 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0019 (x : Var) (y : Var) : (nb068_alpha_dummy_010 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_010, fv_syn_c1c] using (nb068_compact_fv_empty_0019 x y)

theorem nb068_compact_fv_empty_0020 : (nb068_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0020 : (nb068_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_002, fv_syn_c1c] using (nb068_compact_fv_empty_0020)

theorem nb068_compact_fv_empty_0021 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0021 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb068_compact_fv_empty_0021 y)

theorem nb068_compact_fv_empty_0022 : (nb068_alpha_dummy_001) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0022 : (nb068_alpha_dummy_001) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_001, fv_syn_c1c] using (nb068_compact_fv_empty_0022)

theorem nb068_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0023 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb068_compact_fv_empty_0023 x)

theorem nb068_compact_fv_empty_0024 : (nb068_alpha_dummy_003) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0024 : (nb068_alpha_dummy_003) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_003, fv_syn_c1c] using (nb068_compact_fv_empty_0024)

theorem nb068_compact_fv_empty_0025 (x : Var) (y : Var) (f : Var) : (nb068_alpha_dummy_004 x y f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0025 (x : Var) (y : Var) (f : Var) : (nb068_alpha_dummy_004 x y f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_004, fv_syn_c1c] using (nb068_compact_fv_empty_0025 x y f)

theorem nb068_compact_envfresh_0000 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_021) (nb068_alpha_dummy_024 x y) (nb068_wpp_notmem_0000) (nb068_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_020) (nb068_alpha_dummy_023 x y) (nb068_wpp_notmem_0002) (nb068_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_019) (nb068_alpha_dummy_022 x y) (nb068_wpp_notmem_0004) (nb068_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_017) (nb068_alpha_dummy_018 x y) (nb068_wpp_notmem_0006) (nb068_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_013) (nb068_alpha_dummy_015 x y) (nb068_wpp_notmem_0008) (nb068_wpp_notmem_0009 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_014) (nb068_alpha_dummy_016 x y) (nb068_wpp_notmem_0010) (nb068_wpp_notmem_0011 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_006) (nb068_alpha_dummy_008 x y) (nb068_wpp_notmem_0012) (nb068_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_005) (nb068_alpha_dummy_007 x y) (nb068_wpp_notmem_0014) (nb068_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_011) (nb068_alpha_dummy_012 x y) (nb068_wpp_notmem_0016) (nb068_wpp_notmem_0017 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_009) (nb068_alpha_dummy_010 x y) (nb068_wpp_notmem_0018) (nb068_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb068_wpp_refl_0000 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0000 x y f)

theorem nb068_wpp_notmem_0026 : (nb068_alpha_dummy_021) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_021, fv_syn_c0] using (nb068_compact_fv_empty_0000)

theorem nb068_wpp_notmem_0027 (x : Var) (y : Var) : (nb068_alpha_dummy_024 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_024, fv_syn_c0] using (nb068_compact_fv_empty_0001 x y)

theorem nb068_wpp_notmem_0028 : (nb068_alpha_dummy_020) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_020, fv_syn_c0] using (nb068_compact_fv_empty_0002)

theorem nb068_wpp_notmem_0029 (x : Var) (y : Var) : (nb068_alpha_dummy_023 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_023, fv_syn_c0] using (nb068_compact_fv_empty_0003 x y)

theorem nb068_wpp_notmem_0030 : (nb068_alpha_dummy_019) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_019, fv_syn_c0] using (nb068_compact_fv_empty_0004)

theorem nb068_wpp_notmem_0031 (x : Var) (y : Var) : (nb068_alpha_dummy_022 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_022, fv_syn_c0] using (nb068_compact_fv_empty_0005 x y)

theorem nb068_wpp_notmem_0032 : (nb068_alpha_dummy_017) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_017, fv_syn_c0] using (nb068_compact_fv_empty_0006)

theorem nb068_wpp_notmem_0033 (x : Var) (y : Var) : (nb068_alpha_dummy_018 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_018, fv_syn_c0] using (nb068_compact_fv_empty_0007 x y)

theorem nb068_wpp_notmem_0034 : (nb068_alpha_dummy_013) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_013, fv_syn_c0] using (nb068_compact_fv_empty_0008)

theorem nb068_wpp_notmem_0035 (x : Var) (y : Var) : (nb068_alpha_dummy_015 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_015, fv_syn_c0] using (nb068_compact_fv_empty_0009 x y)

theorem nb068_wpp_notmem_0036 : (nb068_alpha_dummy_014) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_014, fv_syn_c0] using (nb068_compact_fv_empty_0010)

theorem nb068_wpp_notmem_0037 (x : Var) (y : Var) : (nb068_alpha_dummy_016 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_016, fv_syn_c0] using (nb068_compact_fv_empty_0011 x y)

theorem nb068_wpp_notmem_0038 : (nb068_alpha_dummy_006) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_006, fv_syn_c0] using (nb068_compact_fv_empty_0012)

theorem nb068_wpp_notmem_0039 (x : Var) (y : Var) : (nb068_alpha_dummy_008 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_008, fv_syn_c0] using (nb068_compact_fv_empty_0013 x y)

theorem nb068_wpp_notmem_0040 : (nb068_alpha_dummy_005) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_005, fv_syn_c0] using (nb068_compact_fv_empty_0014)

theorem nb068_wpp_notmem_0041 (x : Var) (y : Var) : (nb068_alpha_dummy_007 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_007, fv_syn_c0] using (nb068_compact_fv_empty_0015 x y)

theorem nb068_wpp_notmem_0042 : (nb068_alpha_dummy_011) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_011, fv_syn_c0] using (nb068_compact_fv_empty_0016)

theorem nb068_wpp_notmem_0043 (x : Var) (y : Var) : (nb068_alpha_dummy_012 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_012, fv_syn_c0] using (nb068_compact_fv_empty_0017 x y)

theorem nb068_wpp_notmem_0044 : (nb068_alpha_dummy_009) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_009, fv_syn_c0] using (nb068_compact_fv_empty_0018)

theorem nb068_wpp_notmem_0045 (x : Var) (y : Var) : (nb068_alpha_dummy_010 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_010, fv_syn_c0] using (nb068_compact_fv_empty_0019 x y)

theorem nb068_wpp_notmem_0046 : (nb068_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_002, fv_syn_c0] using (nb068_compact_fv_empty_0020)

theorem nb068_wpp_notmem_0047 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb068_compact_fv_empty_0021 y)

theorem nb068_wpp_notmem_0048 : (nb068_alpha_dummy_001) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_001, fv_syn_c0] using (nb068_compact_fv_empty_0022)

theorem nb068_wpp_notmem_0049 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb068_compact_fv_empty_0023 x)

theorem nb068_wpp_notmem_0050 : (nb068_alpha_dummy_003) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_003, fv_syn_c0] using (nb068_compact_fv_empty_0024)

theorem nb068_wpp_notmem_0051 (x : Var) (y : Var) (f : Var) : (nb068_alpha_dummy_004 x y f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_004, fv_syn_c0] using (nb068_compact_fv_empty_0025 x y f)

theorem nb068_compact_envfresh_0001 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_021) (nb068_alpha_dummy_024 x y) (nb068_wpp_notmem_0026) (nb068_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_020) (nb068_alpha_dummy_023 x y) (nb068_wpp_notmem_0028) (nb068_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_019) (nb068_alpha_dummy_022 x y) (nb068_wpp_notmem_0030) (nb068_wpp_notmem_0031 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_017) (nb068_alpha_dummy_018 x y) (nb068_wpp_notmem_0032) (nb068_wpp_notmem_0033 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_013) (nb068_alpha_dummy_015 x y) (nb068_wpp_notmem_0034) (nb068_wpp_notmem_0035 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_014) (nb068_alpha_dummy_016 x y) (nb068_wpp_notmem_0036) (nb068_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_006) (nb068_alpha_dummy_008 x y) (nb068_wpp_notmem_0038) (nb068_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_005) (nb068_alpha_dummy_007 x y) (nb068_wpp_notmem_0040) (nb068_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_011) (nb068_alpha_dummy_012 x y) (nb068_wpp_notmem_0042) (nb068_wpp_notmem_0043 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_009) (nb068_alpha_dummy_010 x y) (nb068_wpp_notmem_0044) (nb068_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb068_wpp_refl_0001 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0001 x y f)

noncomputable def nb068_split_alpha_0000 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_019)) (syn_cun (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_022 x y)) (syn_cun (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0017 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0023 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0021 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0016) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0017 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0023 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0021 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_021), (nb068_alpha_dummy_024 x y)), ((nb068_alpha_dummy_020), (nb068_alpha_dummy_023 x y)), ((nb068_alpha_dummy_019), (nb068_alpha_dummy_022 x y)), ((nb068_alpha_dummy_017), (nb068_alpha_dummy_018 x y)), ((nb068_alpha_dummy_013), (nb068_alpha_dummy_015 x y)), ((nb068_alpha_dummy_014), (nb068_alpha_dummy_016 x y)), ((nb068_alpha_dummy_006), (nb068_alpha_dummy_008 x y)), ((nb068_alpha_dummy_005), (nb068_alpha_dummy_007 x y)), ((nb068_alpha_dummy_011), (nb068_alpha_dummy_012 x y)), ((nb068_alpha_dummy_009), (nb068_alpha_dummy_010 x y)), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0001 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0027 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0025 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0026) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0027 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0025 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0031 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0029 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0030) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0031 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0028) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0029 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_0052 : (nb068_alpha_dummy_017) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_017, fv_syn_cnnc] using (nb068_compact_fv_empty_0006)

theorem nb068_wpp_notmem_0053 (x : Var) (y : Var) : (nb068_alpha_dummy_018 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_018, fv_syn_cnnc] using (nb068_compact_fv_empty_0007 x y)

theorem nb068_wpp_notmem_0054 : (nb068_alpha_dummy_013) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_013, fv_syn_cnnc] using (nb068_compact_fv_empty_0008)

theorem nb068_wpp_notmem_0055 (x : Var) (y : Var) : (nb068_alpha_dummy_015 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_015, fv_syn_cnnc] using (nb068_compact_fv_empty_0009 x y)

theorem nb068_wpp_notmem_0056 : (nb068_alpha_dummy_014) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_014, fv_syn_cnnc] using (nb068_compact_fv_empty_0010)

theorem nb068_wpp_notmem_0057 (x : Var) (y : Var) : (nb068_alpha_dummy_016 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_016, fv_syn_cnnc] using (nb068_compact_fv_empty_0011 x y)

theorem nb068_wpp_notmem_0058 : (nb068_alpha_dummy_006) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_006, fv_syn_cnnc] using (nb068_compact_fv_empty_0012)

theorem nb068_wpp_notmem_0059 (x : Var) (y : Var) : (nb068_alpha_dummy_008 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_008, fv_syn_cnnc] using (nb068_compact_fv_empty_0013 x y)

theorem nb068_wpp_notmem_0060 : (nb068_alpha_dummy_005) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_005, fv_syn_cnnc] using (nb068_compact_fv_empty_0014)

theorem nb068_wpp_notmem_0061 (x : Var) (y : Var) : (nb068_alpha_dummy_007 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_007, fv_syn_cnnc] using (nb068_compact_fv_empty_0015 x y)

theorem nb068_wpp_notmem_0062 : (nb068_alpha_dummy_011) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_011, fv_syn_cnnc] using (nb068_compact_fv_empty_0016)

theorem nb068_wpp_notmem_0063 (x : Var) (y : Var) : (nb068_alpha_dummy_012 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_012, fv_syn_cnnc] using (nb068_compact_fv_empty_0017 x y)

theorem nb068_wpp_notmem_0064 : (nb068_alpha_dummy_009) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_009, fv_syn_cnnc] using (nb068_compact_fv_empty_0018)

theorem nb068_wpp_notmem_0065 (x : Var) (y : Var) : (nb068_alpha_dummy_010 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_010, fv_syn_cnnc] using (nb068_compact_fv_empty_0019 x y)

theorem nb068_wpp_notmem_0066 : (nb068_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_002, fv_syn_cnnc] using (nb068_compact_fv_empty_0020)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
