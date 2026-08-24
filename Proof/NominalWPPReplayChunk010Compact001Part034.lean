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
import NominalWPPReplayChunk010Compact001Part033

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

noncomputable def g_phi011lem1
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (syn_wss (syn_cphi A) (syn_cphi B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((syn_c0c)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cphi A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cphi B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Wff.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ssun1 (syn_cphi A) (syn_csn (syn_c0c))
  have p0001 :=
    @g_sseli (syn_cphi A) (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (.cv z) p0000
  have p0002 :=
    @g_eleq2 (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c))) (.cv z)
  have p0003 :=
    @g_syl5ib (.classMem (.cv z) (syn_cphi A)) (.classMem (.cv z) (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))) (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) p0001 p0002
  have p0004 :=
    @g_n_0cnelphi A
  have p0005 :=
    @g_eleq1 (.cv z) (syn_c0c) (syn_cphi A)
  have p0006 :=
    @g_mtbiri (.classEq (.cv z) (syn_c0c)) (.classMem (.cv z) (syn_cphi A)) (.classMem (syn_c0c) (syn_cphi A)) p0004 p0005
  have p0007 :=
    @g_con2i (.classEq (.cv z) (syn_c0c)) (.classMem (.cv z) (syn_cphi A)) p0006
  have p0008 :=
    @g_a1i (.imp (.classMem (.cv z) (syn_cphi A)) (.neg (.classEq (.cv z) (syn_c0c)))) (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) p0007
  have p0009 :=
    @g_elun (.cv z) (syn_cphi B) (syn_csn (syn_c0c))
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn z (syn_c0c) dv_cache_0001
  have p0011 :=
    @g_eqabri (.classEq (.cv z) (syn_c0c)) z (syn_csn (syn_c0c)) p0010
  have p0012 :=
    @g_orbi2i (.classMem (.cv z) (syn_csn (syn_c0c))) (.classEq (.cv z) (syn_c0c)) (.classMem (.cv z) (syn_cphi B)) p0011
  have p0013 :=
    @g_bitri (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (syn_wo (.classMem (.cv z) (syn_cphi B)) (.classMem (.cv z) (syn_csn (syn_c0c)))) (syn_wo (.classMem (.cv z) (syn_cphi B)) (.classEq (.cv z) (syn_c0c))) p0009 p0012
  have p0014 :=
    @g_biimpi (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (syn_wo (.classMem (.cv z) (syn_cphi B)) (.classEq (.cv z) (syn_c0c))) p0013
  have p0015 :=
    @g_orcomd (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (.classMem (.cv z) (syn_cphi B)) (.classEq (.cv z) (syn_c0c)) p0014
  have p0016 :=
    @g_ord (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (.classEq (.cv z) (syn_c0c)) (.classMem (.cv z) (syn_cphi B)) p0015
  have p0017 :=
    @g_ee22 (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (.classMem (.cv z) (syn_cphi A)) (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (.neg (.classEq (.cv z) (syn_c0c))) (.classMem (.cv z) (syn_cphi B)) p0003 p0008 p0016
  have p0018 :=
    @g_ssrdv (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) z (syn_cphi A) (syn_cphi B) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0017
  exact p0018

noncomputable def g_phi011
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq A B) (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_phi11 A B
  have p0001 :=
    @g_uneq1 (syn_cphi A) (syn_cphi B) (syn_csn (syn_c0c))
  have p0002 :=
    @g_phi011lem1 A B
  have p0003 :=
    @g_phi011lem1 B A
  have p0004 :=
    @g_eqcoms (syn_wss (syn_cphi B) (syn_cphi A)) (syn_cun (syn_cphi B) (syn_csn (syn_c0c))) (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) p0003
  have p0005 :=
    @g_eqssd (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (syn_cphi A) (syn_cphi B) p0002 p0004
  have p0006 :=
    @g_impbii (.classEq (syn_cphi A) (syn_cphi B)) (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) p0001 p0005
  have p0007 :=
    @g_bitri (.classEq A B) (.classEq (syn_cphi A) (syn_cphi B)) (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) p0000 p0006
  exact p0007

noncomputable def g_proj1op
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cproj1 (syn_cop A B)) A) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv x) (syn_cphi (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cphi (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.classMem (.cv z) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_wrex y B (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cop A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Wff.classMem (syn_cphi (.cv z)) (syn_cop A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_cproj1 (syn_cop A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eleq2i (syn_cop A B) (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) (syn_cphi (.cv z)) p0000
  have p0002 :=
    @g_elun (syn_cphi (.cv z)) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
  have p0003 :=
    @g_vex z
  have p0004 :=
    @g_phiex (.cv z) p0003
  have p0005 :=
    @g_eqeq1 (.cv x) (syn_cphi (.cv z)) (syn_cphi (.cv y))
  have p0006 :=
    @g_phi11 (.cv z) (.cv y)
  have p0007 :=
    @g_equcom z y
  have p0008_e00_recanon : Nominal.NPrf (syn_wb (.objEq z y) (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0006
  have p0008 :=
    @g_bitr3i (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y))) (.objEq z y) (.objEq y z) p0008_e00_recanon p0007
  have p0009 :=
    @g_syl6bb (.classEq (.cv x) (syn_cphi (.cv z))) (.classEq (.cv x) (syn_cphi (.cv y))) (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y))) (.objEq y z) p0005 p0008
  have p0010 :=
    @g_rexbidv (.classEq (.cv x) (syn_cphi (.cv z))) (.classEq (.cv x) (syn_cphi (.cv y))) (.objEq y z) y A dv_cache_0006 p0009
  have p0011 :=
    @g_risset y (.cv z) A dv_cache_0007 dv_cache_0002
  have p0012_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv z) A) (syn_wrex y A (.objEq y z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0011
  have p0012 :=
    @g_syl6bbr (.classEq (.cv x) (syn_cphi (.cv z))) (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y A (.objEq y z)) (.classMem (.cv z) A) p0010 p0012_e01_recanon
  have p0013 :=
    @g_elab (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))) (.classMem (.cv z) A) x (syn_cphi (.cv z)) dv_cache_0008 dv_cache_0009 p0004 p0012
  have p0014 :=
    @g_eqeq1 (.cv x) (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))
  have p0015 :=
    @g_rexbidv (.classEq (.cv x) (syn_cphi (.cv z))) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y B dv_cache_0006 p0014
  have p0016 :=
    @g_elab (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (syn_wrex y B (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) x (syn_cphi (.cv z)) dv_cache_0008 dv_cache_0010 p0004 p0015
  have p0017 :=
    @g_orbi12i (.classMem (syn_cphi (.cv z)) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))))) (.classMem (.cv z) A) (.classMem (syn_cphi (.cv z)) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) (syn_wrex y B (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) p0013 p0016
  have p0018 :=
    @g_n_3bitri (.classMem (syn_cphi (.cv z)) (syn_cop A B)) (.classMem (syn_cphi (.cv z)) (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))) (syn_wo (.classMem (syn_cphi (.cv z)) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))))) (.classMem (syn_cphi (.cv z)) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))) (syn_wo (.classMem (.cv z) A) (syn_wrex y B (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) p0001 p0002 p0017
  have p0019 :=
    @g_phieq (.cv x) (.cv z)
  have p0020_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_cphi (.cv x)) (syn_cphi (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0019
  have p0020 :=
    @g_eleq1d (.objEq x z) (syn_cphi (.cv x)) (syn_cphi (.cv z)) (syn_cop A B) p0020_e00_recanon
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_proj1 x (syn_cop A B) dv_cache_0011
  have p0022_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb (.classMem (syn_cphi (.cv x)) (syn_cop A B)) (.classMem (syn_cphi (.cv z)) (syn_cop A B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0020
  have p0022 :=
    @g_elab2 (.classMem (syn_cphi (.cv x)) (syn_cop A B)) (.classMem (syn_cphi (.cv z)) (syn_cop A B)) x (.cv z) (syn_cproj1 (syn_cop A B)) dv_cache_0012 dv_cache_0013 p0003 p0022_e01_recanon p0021
  have p0023 :=
    @g_n_0cnelphi (.cv z)
  have p0024 :=
    @g_ssun2 (syn_csn (syn_c0c)) (syn_cphi (.cv y))
  have p0025 :=
    @g_n_0cex
  have p0026 :=
    @g_snid (syn_c0c) p0025
  have p0027 :=
    @g_sselii (syn_csn (syn_c0c)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) (syn_c0c) p0024 p0026
  have p0028 :=
    @g_eleq2 (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) (syn_c0c)
  have p0029 :=
    @g_mpbiri (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classMem (syn_c0c) (syn_cphi (.cv z))) (.classMem (syn_c0c) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) p0027 p0028
  have p0030 :=
    @g_mto (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classMem (syn_c0c) (syn_cphi (.cv z))) p0023 p0029
  have p0031 :=
    @g_a1i (.neg (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (.classMem (.cv y) B) p0030
  have p0032 :=
    @g_nrex (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y B p0031
  have p0033 :=
    @g_biorfi (syn_wrex y B (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (.classMem (.cv z) A) p0032
  have p0034 :=
    @g_n_3bitr4i (.classMem (syn_cphi (.cv z)) (syn_cop A B)) (syn_wo (.classMem (.cv z) A) (syn_wrex y B (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) (.classMem (.cv z) (syn_cproj1 (syn_cop A B))) (.classMem (.cv z) A) p0018 p0022 p0033
  have p0035 :=
    @g_eqriv z (syn_cproj1 (syn_cop A B)) A dv_cache_0014 dv_cache_0015 p0034
  exact p0035

noncomputable def g_proj2op
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cproj2 (syn_cop A B)) B) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_z, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_wrex y B (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cop A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Wff.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_cproj2 (syn_cop A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eleq2i (syn_cop A B) (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) p0000
  have p0002 :=
    @g_elun (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
  have p0003 :=
    @g_vex z
  have p0004 :=
    @g_phiex (.cv z) p0003
  have p0005 :=
    @g_snex (syn_c0c)
  have p0006 :=
    @g_unex (syn_cphi (.cv z)) (syn_csn (syn_c0c)) p0004 p0005
  have p0007 :=
    @g_eqeq1 (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))
  have p0008 :=
    @g_rexbidv (.classEq (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))) (.classEq (.cv x) (syn_cphi (.cv y))) (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))) y A dv_cache_0006 p0007
  have p0009 :=
    @g_elab (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))) x (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) dv_cache_0007 dv_cache_0008 p0006 p0008
  have p0010 :=
    @g_phi011 (.cv z) (.cv y)
  have p0011 :=
    @g_equcom z y
  have p0012_e00_recanon : Nominal.NPrf (syn_wb (.objEq z y) (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cphi syn_wrex syn_wex syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c syn_csn syn_c0c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0010
  have p0012 :=
    @g_bitr3i (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.objEq z y) (.objEq y z) p0012_e00_recanon p0011
  have p0013 :=
    @g_rexbii (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.objEq y z) y B p0012
  have p0014 :=
    @g_eqeq1 (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))
  have p0015 :=
    @g_rexbidv (.classEq (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y B dv_cache_0006 p0014
  have p0016 :=
    @g_elab (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (syn_wrex y B (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) x (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) dv_cache_0007 dv_cache_0009 p0006 p0015
  have p0017 :=
    @g_risset y (.cv z) B dv_cache_0010 dv_cache_0004
  have p0018_e02_recanon : Nominal.NPrf (syn_wb (.classMem (.cv z) B) (syn_wrex y B (.objEq y z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0017
  have p0018 :=
    @g_n_3bitr4i (syn_wrex y B (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (syn_wrex y B (.objEq y z)) (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) (.classMem (.cv z) B) p0013 p0016 p0018_e02_recanon
  have p0019 :=
    @g_orbi12i (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))))) (syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))) (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) (.classMem (.cv z) B) p0009 p0018
  have p0020 :=
    @g_bitri (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))) (syn_wo (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))))) (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))) (syn_wo (syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))) (.classMem (.cv z) B)) p0002 p0019
  have p0021 :=
    @g_bitri (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B)) (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))) (syn_wo (syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))) (.classMem (.cv z) B)) p0001 p0020
  have p0022 :=
    @g_phieq (.cv x) (.cv z)
  have p0023_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_cphi (.cv x)) (syn_cphi (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0022
  have p0023 :=
    @g_uneq1d (.objEq x z) (syn_cphi (.cv x)) (syn_cphi (.cv z)) (syn_csn (syn_c0c)) p0023_e00_recanon
  have p0024 :=
    @g_eleq1d (.objEq x z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B) p0023
  have p0025 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_proj2 x (syn_cop A B) dv_cache_0011
  have p0026_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb (.classMem (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) (syn_cop A B)) (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cphi syn_wrex syn_wex syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c syn_csn syn_c0c syn_cop
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0024
  have p0026 :=
    @g_elab2 (.classMem (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) (syn_cop A B)) (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B)) x (.cv z) (syn_cproj2 (syn_cop A B)) dv_cache_0012 dv_cache_0013 p0003 p0026_e01_recanon p0025
  have p0027 :=
    @g_n_0cnelphi (.cv y)
  have p0028 :=
    @g_ssun2 (syn_csn (syn_c0c)) (syn_cphi (.cv z))
  have p0029 :=
    @g_n_0cex
  have p0030 :=
    @g_snid (syn_c0c) p0029
  have p0031 :=
    @g_sselii (syn_csn (syn_c0c)) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_c0c) p0028 p0030
  have p0032 :=
    @g_eleq2 (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)) (syn_c0c)
  have p0033 :=
    @g_mpbii (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))) (.classMem (syn_c0c) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))) (.classMem (syn_c0c) (syn_cphi (.cv y))) p0031 p0032
  have p0034 :=
    @g_mto (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))) (.classMem (syn_c0c) (syn_cphi (.cv y))) p0027 p0033
  have p0035 :=
    @g_a1i (.neg (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))) (.classMem (.cv y) A) p0034
  have p0036 :=
    @g_nrex (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))) y A p0035
  have p0037 :=
    @g_biorfi (syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))) (.classMem (.cv z) B) p0036
  have p0038 :=
    @g_orcom (.classMem (.cv z) B) (syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
  have p0039 :=
    @g_bitri (.classMem (.cv z) B) (syn_wo (.classMem (.cv z) B) (syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))) (syn_wo (syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))) (.classMem (.cv z) B)) p0037 p0038
  have p0040 :=
    @g_n_3bitr4i (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B)) (syn_wo (syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))) (.classMem (.cv z) B)) (.classMem (.cv z) (syn_cproj2 (syn_cop A B))) (.classMem (.cv z) B) p0021 p0026 p0039
  have p0041 :=
    @g_eqriv z (syn_cproj2 (syn_cop A B)) B dv_cache_0014 dv_cache_0015 p0040
  exact p0041

noncomputable def g_opth
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (syn_wb (.classEq (syn_cop A B) (syn_cop C D)) (syn_wa (.classEq A C) (.classEq B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_proj1eq (syn_cop A B) (syn_cop C D)
  have p0001 :=
    @g_proj1op A B
  have p0002 :=
    @g_proj1op C D
  have p0003 :=
    @g_n_3eqtr3g (.classEq (syn_cop A B) (syn_cop C D)) (syn_cproj1 (syn_cop A B)) (syn_cproj1 (syn_cop C D)) A C p0000 p0001 p0002
  have p0004 :=
    @g_proj2eq (syn_cop A B) (syn_cop C D)
  have p0005 :=
    @g_proj2op A B
  have p0006 :=
    @g_proj2op C D
  have p0007 :=
    @g_n_3eqtr3g (.classEq (syn_cop A B) (syn_cop C D)) (syn_cproj2 (syn_cop A B)) (syn_cproj2 (syn_cop C D)) B D p0004 p0005 p0006
  have p0008 :=
    @g_jca (.classEq (syn_cop A B) (syn_cop C D)) (.classEq A C) (.classEq B D) p0003 p0007
  have p0009 :=
    @g_opeq12 A C B D
  have p0010 :=
    @g_impbii (.classEq (syn_cop A B) (syn_cop C D)) (syn_wa (.classEq A C) (.classEq B D)) p0008 p0009
  exact p0010

noncomputable def g_opexb
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop A B) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_proj1op A B
  have p0001 :=
    @g_proj1exg (syn_cop A B) (syn_cvv)
  have p0002 :=
    @g_syl5eqelr (.classMem (syn_cop A B) (syn_cvv)) A (syn_cproj1 (syn_cop A B)) (syn_cvv) p0000 p0001
  have p0003 :=
    @g_proj2op A B
  have p0004 :=
    @g_proj2exg (syn_cop A B) (syn_cvv)
  have p0005 :=
    @g_syl5eqelr (.classMem (syn_cop A B) (syn_cvv)) B (syn_cproj2 (syn_cop A B)) (syn_cvv) p0003 p0004
  have p0006 :=
    @g_jca (.classMem (syn_cop A B) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_opexg A B (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_impbii (.classMem (syn_cop A B) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0006 p0007
  exact p0008

#print axioms g_opexb

end NFChoice.DirectNominalPrf.WPPReplay
