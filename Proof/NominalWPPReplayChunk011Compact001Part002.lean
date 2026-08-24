import WPPCompactSourceSyntax
import WPPCompactSyntaxFVExplicit
import CompactSyntaxFV
import CoreFVSimp
import NominalSubstitutionLemmas
import NominalDefinitionRefl
import NominalDfEu
import NominalAlphaRepairedDfNfc001
import NominalAlphaRepairedBase001003V
import NominalAlphaRepairedBase001004Csb
import NominalAlphaRepairedBase001005Nin
import NominalAlphaRepairedBase001006If
import NominalAlphaRepairedBase001007Pw
import NominalAlphaRepairedBase001008Sn
import NominalAlphaRepairedBase001009Uni
import NominalAlphaRepairedBase001010Int
import NominalAlphaRepairedBase001011Iun
import NominalAlphaRepairedBase001012Leaf1c
import NominalAlphaRepairedBase001013Xpk
import NominalAlphaRepairedBase001014Cnvk
import NominalAlphaRepairedBase001015Ins2k
import NominalAlphaRepairedBase001016Ins3k
import NominalAlphaRepairedBase001017Imak
import NominalAlphaRepairedBase001018P6
import NominalAlphaRepairedBase001019Sik
import NominalAlphaRepairedBase001020Ssetk
import NominalAlphaRepairedBase001021Idk
import NominalAlphaRepairedBase001022Iota
import NominalAlphaRepairedBase001023Addc
import NominalAlphaRepairedBase001024Nnc
import NominalAlphaRepairedBase001025Lefin
import NominalAlphaRepairedBase001026Ltfin
import NominalAlphaRepairedBase001027Ncfin
import NominalAlphaRepairedBase001028Tfin
import NominalAlphaRepairedBase001029Evenfin
import NominalAlphaRepairedBase001030Oddfin
import NominalAlphaRepairedBase001031Sfin
import NominalAlphaRepairedBase001032Spfin
import NominalAlphaRepairedBase001033Phi
import NominalAlphaRepairedBase001034OpReflected001
import NominalAlphaRepairedBase001035Proj1Reflected001
import NominalAlphaRepairedBase001036Proj2Reflected001
import NominalAlphaRepairedBase001037OpabOpaqueHoisted004
import NominalAlphaRepairedBase001038Leaf1stReflected001
import NominalAlphaRepairedBase001039SwapReflected001
import NominalAlphaRepairedBase001040SsetReflected001
import NominalAlphaRepairedBase001041CoReflected001
import NominalAlphaRepairedBase001042ImaReflected001
import NominalAlphaRepairedBase001043SiReflected001
import NominalAlphaRepairedBase001044IdReflected001
import NominalAlphaRepairedBase001045XpReflected001
import NominalAlphaRepairedBase001046CnvReflected001
import NominalAlphaRepairedBase001047FvReflected001
import NominalAlphaRepairedBase001048Leaf2ndReflected001
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk011Compact001Part001

set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

noncomputable def g_cnvuni
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cuni A)) (syn_ciun x A (syn_ccnv (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : z ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cuni A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((syn_cuni A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0006 : x ∉ ((syn_cop (.cv w) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classEq (.cv y) (syn_cop (.cv z) (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0013 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0015 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_ccnv (syn_cuni A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_ciun x A (syn_ccnv (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elcnv2 z w (.cv y) (syn_cuni A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eluni2 x (syn_cop (.cv w) (.cv z)) A dv_cache_0006 dv_cache_0007
  have p0002 :=
    @g_anbi2i (.classMem (syn_cop (.cv w) (.cv z)) (syn_cuni A)) (syn_wrex x A (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))) (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) p0001
  have p0003 :=
    @g_r19_42v (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)) x A dv_cache_0008
  have p0004 :=
    @g_bitr4i (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (syn_cuni A))) (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (syn_wrex x A (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))) (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))) p0002 p0003
  have p0005 :=
    @g_n_2exbii (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (syn_cuni A))) (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))) z w p0004
  have p0006 :=
    @g_elcnv2 z w (.cv y) (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0009 dv_cache_0010 dv_cache_0005
  have p0007 :=
    @g_rexbii (.classMem (.cv y) (syn_ccnv (.cv x))) (syn_wex z (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))) x A p0006
  have p0008 :=
    @g_rexcom4 (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))) x z A dv_cache_0011 dv_cache_0012
  have p0009 :=
    @g_rexcom4 (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))) x w A dv_cache_0013 dv_cache_0014
  have p0010 :=
    @g_exbii (syn_wrex x A (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))) (syn_wex w (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))) z p0009
  have p0011 :=
    @g_n_3bitrri (syn_wrex x A (.classMem (.cv y) (syn_ccnv (.cv x)))) (syn_wrex x A (syn_wex z (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))))) (syn_wex z (syn_wrex x A (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))))) (syn_wex z (syn_wex w (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))))) p0007 p0008 p0010
  have p0012 :=
    @g_n_3bitri (.classMem (.cv y) (syn_ccnv (syn_cuni A))) (syn_wex z (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (syn_cuni A))))) (syn_wex z (syn_wex w (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))))) (syn_wrex x A (.classMem (.cv y) (syn_ccnv (.cv x)))) p0000 p0005 p0011
  have p0013 :=
    @g_eliun x (.cv y) A (syn_ccnv (.cv x)) dv_cache_0015
  have p0014 :=
    @g_bitr4i (.classMem (.cv y) (syn_ccnv (syn_cuni A))) (syn_wrex x A (.classMem (.cv y) (syn_ccnv (.cv x)))) (.classMem (.cv y) (syn_ciun x A (syn_ccnv (.cv x)))) p0012 p0013
  have p0015 :=
    @g_eqriv y (syn_ccnv (syn_cuni A)) (syn_ciun x A (syn_ccnv (.cv x))) dv_cache_0016 dv_cache_0017 p0014
  exact p0015

noncomputable def g_elrn
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_crn B)) (syn_wex x (syn_wbr (.cv x) B A))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_crn] using (Nominal.classEqRefl (syn_crn B)))
  have p0001 :=
    @g_eleq2i (syn_crn B) (syn_cima B (syn_cvv)) A p0000
  have p0002 :=
    @g_elima x A B (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @g_rexv (syn_wbr (.cv x) B A) x
  have p0004 :=
    @g_n_3bitri (.classMem A (syn_crn B)) (.classMem A (syn_cima B (syn_cvv))) (syn_wrex x (syn_cvv) (syn_wbr (.cv x) B A)) (syn_wex x (syn_wbr (.cv x) B A)) p0001 p0002 p0003
  exact p0004

noncomputable def g_elrn2
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_crn B)) (syn_wex x (.classMem (syn_cop (.cv x) A) B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elrn x A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) B A)))
  have p0002 :=
    @g_exbii (syn_wbr (.cv x) B A) (.classMem (syn_cop (.cv x) A) B) x p0001
  have p0003 :=
    @g_bitri (.classMem A (syn_crn B)) (syn_wex x (syn_wbr (.cv x) B A)) (syn_wex x (.classMem (syn_cop (.cv x) A) B)) p0000 p0002
  exact p0003

noncomputable def g_eldm
    (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cdm B)) (syn_wex y (syn_wbr A B (.cv y)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cdm] using (Nominal.classEqRefl (syn_cdm B)))
  have p0001 :=
    @g_eleq2i (syn_cdm B) (syn_crn (syn_ccnv B)) A p0000
  have p0002 :=
    @g_elrn y A (syn_ccnv B) dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_bitri (.classMem A (syn_cdm B)) (.classMem A (syn_crn (syn_ccnv B))) (syn_wex y (syn_wbr (.cv y) (syn_ccnv B) A)) p0001 p0002
  have p0004 :=
    @g_brcnv (.cv y) A B
  have p0005 :=
    @g_exbii (syn_wbr (.cv y) (syn_ccnv B) A) (syn_wbr A B (.cv y)) y p0004
  have p0006 :=
    @g_bitri (.classMem A (syn_cdm B)) (syn_wex y (syn_wbr (.cv y) (syn_ccnv B) A)) (syn_wex y (syn_wbr A B (.cv y))) p0003 p0005
  exact p0006

noncomputable def g_eldm2
    (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cdm B)) (syn_wex y (.classMem (syn_cop A (.cv y)) B))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eldm y A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A B (.cv y))))
  have p0002 :=
    @g_exbii (syn_wbr A B (.cv y)) (.classMem (syn_cop A (.cv y)) B) y p0001
  have p0003 :=
    @g_bitri (.classMem A (syn_cdm B)) (syn_wex y (syn_wbr A B (.cv y))) (syn_wex y (.classMem (syn_cop A (.cv y)) B)) p0000 p0002
  exact p0003

noncomputable def g_dfdm2
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cdm A) (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cdm A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eldm y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_eqabi (syn_wex y (syn_wbr (.cv x) A (.cv y))) x (syn_cdm A) dv_cache_0003 p0000
  exact p0001

noncomputable def g_dfdm3
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cdm A) (.cab x (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cdm A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eldm2 y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_eqabi (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)) x (syn_cdm A) dv_cache_0003 p0000
  exact p0001

noncomputable def g_dfrn2
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_crn A) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have dv_cache_0001 : x ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_crn A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elrn x (.cv y) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_eqabi (syn_wex x (syn_wbr (.cv x) A (.cv y))) y (syn_crn A) dv_cache_0003 p0000
  exact p0001

noncomputable def g_dfrn3
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_crn A) (.cab y (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_dfrn2 x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) A (.cv y))))
  have p0002 :=
    @g_exbii (syn_wbr (.cv x) A (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) A) x p0001
  have p0003 :=
    @g_abbii (syn_wex x (syn_wbr (.cv x) A (.cv y))) (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A)) y p0002
  have p0004 :=
    @g_eqtri (syn_crn A) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (.cab y (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A))) p0000 p0003
  exact p0004

noncomputable def g_dfrn4
    (A : Class) :
    Nominal.NPrf (.classEq (syn_crn A) (syn_cdm (syn_ccnv A))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_crn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cdm (syn_ccnv A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brcnv (.cv x) (.cv y) A
  have p0001 :=
    @g_exbii (syn_wbr (.cv x) (syn_ccnv A) (.cv y)) (syn_wbr (.cv y) A (.cv x)) y p0000
  have p0002 :=
    @g_eldm y (.cv x) (syn_ccnv A) dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_elrn y (.cv x) A dv_cache_0001 dv_cache_0003
  have p0004 :=
    @g_n_3bitr4ri (syn_wex y (syn_wbr (.cv x) (syn_ccnv A) (.cv y))) (syn_wex y (syn_wbr (.cv y) A (.cv x))) (.classMem (.cv x) (syn_cdm (syn_ccnv A))) (.classMem (.cv x) (syn_crn A)) p0001 p0002 p0003
  have p0005 :=
    @g_eqriv x (syn_crn A) (syn_cdm (syn_ccnv A)) dv_cache_0004 dv_cache_0005 p0004
  exact p0005

noncomputable def g_dfdmf
    (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y) (hyp_dfdmf_1 : Nominal.NPrf (syn_wnfc x A)) (hyp_dfdmf_2 : Nominal.NPrf (syn_wnfc y A)) :
    Nominal.NPrf (.classEq (syn_cdm A) (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  let w : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_w_ne_v : w ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_w : v ≠ w :=
    Ne.symm fresh_w_ne_v
  have dv_cache_0001 : w ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : w ≠ v := by
    clear dv_cache_0001 dv_cache_0002
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0004 : y ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((syn_wbr (.cv w) A (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_y, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_wex y (syn_wbr (.cv x) A (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Wff.objEq w x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dfdm2 w v A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_nfcv y (.cv w) dv_cache_0004
  have p0002 :=
    @g_nfcv y (.cv v) dv_cache_0005
  have p0003 :=
    @g_nfbr y (.cv w) (.cv v) A p0001 hyp_dfdmf_2 p0002
  have p0004 :=
    @g_nfv (syn_wbr (.cv w) A (.cv y)) v dv_cache_0006
  have p0005 :=
    @g_breq2 (.cv v) (.cv y) (.cv w) A
  have p0006_e02_recanon : Nominal.NPrf (.imp (.objEq v y) (syn_wb (syn_wbr (.cv w) A (.cv v)) (syn_wbr (.cv w) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0006 :=
    @g_cbvex (syn_wbr (.cv w) A (.cv v)) (syn_wbr (.cv w) A (.cv y)) v y p0003 p0004 p0006_e02_recanon
  have p0007 :=
    @g_abbii (syn_wex v (syn_wbr (.cv w) A (.cv v))) (syn_wex y (syn_wbr (.cv w) A (.cv y))) w p0006
  have p0008 :=
    @g_nfcv x (.cv w) dv_cache_0007
  have p0009 :=
    @g_nfcv x (.cv y) dv_cache_0008
  have p0010 :=
    @g_nfbr x (.cv w) (.cv y) A p0008 hyp_dfdmf_1 p0009
  have p0011 :=
    @g_nfex (syn_wbr (.cv w) A (.cv y)) x y p0010
  have p0012 :=
    @g_nfv (syn_wex y (syn_wbr (.cv x) A (.cv y))) w dv_cache_0009
  have p0013 :=
    @g_breq1 (.cv w) (.cv x) (.cv y) A
  have p0014_e00_recanon : Nominal.NPrf (.imp (.objEq w x) (syn_wb (syn_wbr (.cv w) A (.cv y)) (syn_wbr (.cv x) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0013
  have p0014 :=
    @g_exbidv (.objEq w x) (syn_wbr (.cv w) A (.cv y)) (syn_wbr (.cv x) A (.cv y)) y dv_cache_0010 p0014_e00_recanon
  have p0015 :=
    @g_cbvab (syn_wex y (syn_wbr (.cv w) A (.cv y))) (syn_wex y (syn_wbr (.cv x) A (.cv y))) w x p0011 p0012 p0014
  have p0016 :=
    @g_n_3eqtri (syn_cdm A) (.cab w (syn_wex v (syn_wbr (.cv w) A (.cv v)))) (.cab w (syn_wex y (syn_wbr (.cv w) A (.cv y)))) (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y)))) p0000 p0007 p0015
  exact p0016

noncomputable def g_dmss
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cdm A) (syn_cdm B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((syn_wss A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cdm A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cdm B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wss A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ssel A B (syn_cop (.cv x) (.cv y))
  have p0001 :=
    @g_eximdv (syn_wss A B) (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B) y dv_cache_0001 p0000
  have p0002 :=
    @g_eldm2 y (.cv x) A dv_cache_0002 dv_cache_0003
  have p0003 :=
    @g_eldm2 y (.cv x) B dv_cache_0002 dv_cache_0004
  have p0004 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)) (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) B)) (.classMem (.cv x) (syn_cdm A)) (.classMem (.cv x) (syn_cdm B)) p0001 p0002 p0003
  have p0005 :=
    @g_ssrdv (syn_wss A B) x (syn_cdm A) (syn_cdm B) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0004
  exact p0005

noncomputable def g_dmeq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cdm A) (syn_cdm B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dmss A B
  have p0001 :=
    @g_dmss B A
  have p0002 :=
    @g_anim12i (syn_wss A B) (syn_wss (syn_cdm A) (syn_cdm B)) (syn_wss B A) (syn_wss (syn_cdm B) (syn_cdm A)) p0000 p0001
  have p0003 :=
    @g_eqss A B
  have p0004 :=
    @g_eqss (syn_cdm A) (syn_cdm B)
  have p0005 :=
    @g_n_3imtr4i (syn_wa (syn_wss A B) (syn_wss B A)) (syn_wa (syn_wss (syn_cdm A) (syn_cdm B)) (syn_wss (syn_cdm B) (syn_cdm A))) (.classEq A B) (.classEq (syn_cdm A) (syn_cdm B)) p0002 p0003 p0004
  exact p0005

noncomputable def g_dmeqi
    (A : Class) (B : Class) (hyp_dmeqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cdm A) (syn_cdm B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dmeq A B
  have p0001 :=
    Nominal.mp hyp_dmeqi_1 p0000
  exact p0001

noncomputable def g_dmeqd
    (ph : Wff) (A : Class) (B : Class) (hyp_dmeqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cdm A) (syn_cdm B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_dmeq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cdm A) (syn_cdm B)) hyp_dmeqd_1 p0000
  exact p0001

noncomputable def g_opeldm
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem (syn_cop A B) C) (.classMem A (syn_cdm C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classMem (syn_cop A B) C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex (syn_cop A B) C
  have p0001 :=
    @g_opexb A B
  have p0002 :=
    @g_simprbi (.classMem (syn_cop A B) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0001
  have p0003 :=
    @g_syl (.classMem (syn_cop A B) C) (.classMem (syn_cop A B) (syn_cvv)) (.classMem B (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_opeq2 (.cv y) B A
  have p0005 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_cop A (.cv y)) (syn_cop A B) C p0004
  have p0006 :=
    @g_spcegv (.classMem (syn_cop A (.cv y)) C) (.classMem (syn_cop A B) C) y B (syn_cvv) dv_cache_0001 dv_cache_0002 p0005
  have p0007 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem (syn_cop A B) C) (syn_wex y (.classMem (syn_cop A (.cv y)) C)) p0003 p0006
  have p0008 :=
    @g_eldm2 y A C dv_cache_0003 dv_cache_0004
  have p0009 :=
    @g_sylibr (.classMem (syn_cop A B) C) (syn_wex y (.classMem (syn_cop A (.cv y)) C)) (.classMem A (syn_cdm C)) p0007 p0008
  exact p0009

noncomputable def g_breldm
    (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr A R B) (.classMem A (syn_cdm R))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A R B)))
  have p0001 :=
    @g_opeldm A B R
  have p0002 :=
    @g_sylbi (syn_wbr A R B) (.classMem (syn_cop A B) R) (.classMem A (syn_cdm R)) p0000 p0001
  exact p0002

noncomputable def g_dmun
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cun A B)) (syn_cun (syn_cdm A) (syn_cdm B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_cun A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cun A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cun (syn_cdm A) (syn_cdm B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dfdm3 x y (syn_cun A B) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eldm y (.cv x) A dv_cache_0004 dv_cache_0005
  have p0002 :=
    @g_eldm y (.cv x) B dv_cache_0004 dv_cache_0006
  have p0003 :=
    @g_orbi12i (.classMem (.cv x) (syn_cdm A)) (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) (syn_cdm B)) (syn_wex y (syn_wbr (.cv x) B (.cv y))) p0001 p0002
  have p0004 :=
    @g_elun (.cv x) (syn_cdm A) (syn_cdm B)
  have p0005 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cun A B) (.cv y))))
  have p0006 :=
    @g_brun (.cv x) (.cv y) A B
  have p0007 :=
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B)) (syn_wbr (.cv x) (syn_cun A B) (.cv y)) (syn_wo (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y))) p0005 p0006
  have p0008 :=
    @g_exbii (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B)) (syn_wo (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y))) y p0007
  have p0009 :=
    @g_n_19_43 (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y)) y
  have p0010 :=
    @g_bitri (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B))) (syn_wex y (syn_wo (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y)))) (syn_wo (syn_wex y (syn_wbr (.cv x) A (.cv y))) (syn_wex y (syn_wbr (.cv x) B (.cv y)))) p0008 p0009
  have p0011 :=
    @g_n_3bitr4i (syn_wo (.classMem (.cv x) (syn_cdm A)) (.classMem (.cv x) (syn_cdm B))) (syn_wo (syn_wex y (syn_wbr (.cv x) A (.cv y))) (syn_wex y (syn_wbr (.cv x) B (.cv y)))) (.classMem (.cv x) (syn_cun (syn_cdm A) (syn_cdm B))) (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B))) p0003 p0004 p0010
  have p0012 :=
    @g_eqabi (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B))) x (syn_cun (syn_cdm A) (syn_cdm B)) dv_cache_0007 p0011
  have p0013 :=
    @g_eqtr4i (syn_cdm (syn_cun A B)) (.cab x (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B)))) (syn_cun (syn_cdm A) (syn_cdm B)) p0000 p0012
  exact p0013

#print axioms g_dmun

end NFChoice.DirectNominalPrf.WPPReplay
