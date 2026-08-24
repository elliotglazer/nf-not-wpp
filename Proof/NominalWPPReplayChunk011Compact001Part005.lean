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
import NominalWPPReplayChunk011Compact001Part004

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

noncomputable def g_dmcoss
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cdm (syn_ccom A B)) (syn_cdm B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_wbr (.cv x) B (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_ccom A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cdm (syn_ccom A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cdm B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brco z (.cv x) (.cv y) A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_exbii (syn_wbr (.cv x) (syn_ccom A B) (.cv y)) (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))) y p0000
  have p0002 :=
    @g_excom (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))) y z
  have p0003 :=
    @g_bitri (syn_wex y (syn_wbr (.cv x) (syn_ccom A B) (.cv y))) (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))))) (syn_wex z (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))))) p0001 p0002
  have p0004 :=
    @g_simpl (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))
  have p0005 :=
    @g_exlimiv (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))) (syn_wbr (.cv x) B (.cv z)) y dv_cache_0005 p0004
  have p0006 :=
    @g_eximi (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))) (syn_wbr (.cv x) B (.cv z)) z p0005
  have p0007 :=
    @g_sylbi (syn_wex y (syn_wbr (.cv x) (syn_ccom A B) (.cv y))) (syn_wex z (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))))) (syn_wex z (syn_wbr (.cv x) B (.cv z))) p0003 p0006
  have p0008 :=
    @g_eldm y (.cv x) (syn_ccom A B) dv_cache_0006 dv_cache_0007
  have p0009 :=
    @g_eldm z (.cv x) B dv_cache_0001 dv_cache_0004
  have p0010 :=
    @g_n_3imtr4i (syn_wex y (syn_wbr (.cv x) (syn_ccom A B) (.cv y))) (syn_wex z (syn_wbr (.cv x) B (.cv z))) (.classMem (.cv x) (syn_cdm (syn_ccom A B))) (.classMem (.cv x) (syn_cdm B)) p0007 p0008 p0009
  have p0011 :=
    @g_ssriv x (syn_cdm (syn_ccom A B)) (syn_cdm B) dv_cache_0008 dv_cache_0009 p0010
  exact p0011

noncomputable def g_rncoss
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_crn (syn_ccom A B)) (syn_crn A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dmcoss (syn_ccnv B) (syn_ccnv A)
  have p0001 :=
    @g_dfrn4 (syn_ccom A B)
  have p0002 :=
    @g_cnvco A B
  have p0003 :=
    @g_dmeqi (syn_ccnv (syn_ccom A B)) (syn_ccom (syn_ccnv B) (syn_ccnv A)) p0002
  have p0004 :=
    @g_eqtri (syn_crn (syn_ccom A B)) (syn_cdm (syn_ccnv (syn_ccom A B))) (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A))) p0001 p0003
  have p0005 :=
    @g_dfrn4 A
  have p0006 :=
    @g_n_3sstr4i (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A))) (syn_cdm (syn_ccnv A)) (syn_crn (syn_ccom A B)) (syn_crn A) p0000 p0004 p0005
  exact p0006

noncomputable def g_dmcosseq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss (syn_crn B) (syn_cdm A)) (.classEq (syn_cdm (syn_ccom A B)) (syn_cdm B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wbr (.cv x) B (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_wss (syn_crn B) (syn_cdm A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_ccom A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cdm B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cdm (syn_ccom A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_wss (syn_crn B) (syn_cdm A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dmcoss A B
  have p0001 :=
    @g_a1i (syn_wss (syn_cdm (syn_ccom A B)) (syn_cdm B)) (syn_wss (syn_crn B) (syn_cdm A)) p0000
  have p0002 :=
    @g_brelrn (.cv x) (.cv y) B
  have p0003 :=
    @g_ssel (syn_crn B) (syn_cdm A) (.cv y)
  have p0004 :=
    @g_syl5 (syn_wbr (.cv x) B (.cv y)) (.classMem (.cv y) (syn_crn B)) (syn_wss (syn_crn B) (syn_cdm A)) (.classMem (.cv y) (syn_cdm A)) p0002 p0003
  have p0005 :=
    @g_eldm z (.cv y) A dv_cache_0001 dv_cache_0002
  have p0006 :=
    @g_syl6ib (syn_wss (syn_crn B) (syn_cdm A)) (syn_wbr (.cv x) B (.cv y)) (.classMem (.cv y) (syn_cdm A)) (syn_wex z (syn_wbr (.cv y) A (.cv z))) p0004 p0005
  have p0007 :=
    @g_ancld (syn_wss (syn_crn B) (syn_cdm A)) (syn_wbr (.cv x) B (.cv y)) (syn_wex z (syn_wbr (.cv y) A (.cv z))) p0006
  have p0008 :=
    @g_n_19_42v (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)) z dv_cache_0003
  have p0009 :=
    @g_syl6ibr (syn_wss (syn_crn B) (syn_cdm A)) (syn_wbr (.cv x) B (.cv y)) (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wex z (syn_wbr (.cv y) A (.cv z)))) (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)))) p0007 p0008
  have p0010 :=
    @g_eximdv (syn_wss (syn_crn B) (syn_cdm A)) (syn_wbr (.cv x) B (.cv y)) (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)))) y dv_cache_0004 p0009
  have p0011 :=
    @g_brco y (.cv x) (.cv z) A B dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0012 :=
    @g_exbii (syn_wbr (.cv x) (syn_ccom A B) (.cv z)) (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)))) z p0011
  have p0013 :=
    @g_excom (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z))) z y
  have p0014 :=
    @g_bitri (syn_wex z (syn_wbr (.cv x) (syn_ccom A B) (.cv z))) (syn_wex z (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z))))) (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z))))) p0012 p0013
  have p0015 :=
    @g_syl6ibr (syn_wss (syn_crn B) (syn_cdm A)) (syn_wex y (syn_wbr (.cv x) B (.cv y))) (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z))))) (syn_wex z (syn_wbr (.cv x) (syn_ccom A B) (.cv z))) p0010 p0014
  have p0016 :=
    @g_eldm y (.cv x) B dv_cache_0005 dv_cache_0008
  have p0017 :=
    @g_eldm z (.cv x) (syn_ccom A B) dv_cache_0009 dv_cache_0010
  have p0018 :=
    @g_n_3imtr4g (syn_wss (syn_crn B) (syn_cdm A)) (syn_wex y (syn_wbr (.cv x) B (.cv y))) (syn_wex z (syn_wbr (.cv x) (syn_ccom A B) (.cv z))) (.classMem (.cv x) (syn_cdm B)) (.classMem (.cv x) (syn_cdm (syn_ccom A B))) p0015 p0016 p0017
  have p0019 :=
    @g_ssrdv (syn_wss (syn_crn B) (syn_cdm A)) x (syn_cdm B) (syn_cdm (syn_ccom A B)) dv_cache_0011 dv_cache_0012 dv_cache_0013 p0018
  have p0020 :=
    @g_eqssd (syn_wss (syn_crn B) (syn_cdm A)) (syn_cdm (syn_ccom A B)) (syn_cdm B) p0001 p0019
  exact p0020

noncomputable def g_dmcoeq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq (syn_cdm A) (syn_crn B)) (.classEq (syn_cdm (syn_ccom A B)) (syn_cdm B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_eqimss2 (syn_crn B) (syn_cdm A)
  have p0001 :=
    @g_dmcosseq A B
  have p0002 :=
    @g_syl (.classEq (syn_cdm A) (syn_crn B)) (syn_wss (syn_crn B) (syn_cdm A)) (.classEq (syn_cdm (syn_ccom A B)) (syn_cdm B)) p0000 p0001
  exact p0002

noncomputable def g_rncoeq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq (syn_cdm A) (syn_crn B)) (.classEq (syn_crn (syn_ccom A B)) (syn_crn A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dmcoeq (syn_ccnv B) (syn_ccnv A)
  have p0001 :=
    (by simpa [syn_cdm] using (Nominal.classEqRefl (syn_cdm A)))
  have p0002 :=
    @g_dfrn4 B
  have p0003 :=
    @g_eqeq12i (syn_cdm A) (syn_crn (syn_ccnv A)) (syn_crn B) (syn_cdm (syn_ccnv B)) p0001 p0002
  have p0004 :=
    @g_eqcom (syn_crn (syn_ccnv A)) (syn_cdm (syn_ccnv B))
  have p0005 :=
    @g_bitri (.classEq (syn_cdm A) (syn_crn B)) (.classEq (syn_crn (syn_ccnv A)) (syn_cdm (syn_ccnv B))) (.classEq (syn_cdm (syn_ccnv B)) (syn_crn (syn_ccnv A))) p0003 p0004
  have p0006 :=
    @g_dfrn4 (syn_ccom A B)
  have p0007 :=
    @g_cnvco A B
  have p0008 :=
    @g_dmeqi (syn_ccnv (syn_ccom A B)) (syn_ccom (syn_ccnv B) (syn_ccnv A)) p0007
  have p0009 :=
    @g_eqtri (syn_crn (syn_ccom A B)) (syn_cdm (syn_ccnv (syn_ccom A B))) (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A))) p0006 p0008
  have p0010 :=
    @g_dfrn4 A
  have p0011 :=
    @g_eqeq12i (syn_crn (syn_ccom A B)) (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A))) (syn_crn A) (syn_cdm (syn_ccnv A)) p0009 p0010
  have p0012 :=
    @g_n_3imtr4i (.classEq (syn_cdm (syn_ccnv B)) (syn_crn (syn_ccnv A))) (.classEq (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A))) (syn_cdm (syn_ccnv A))) (.classEq (syn_cdm A) (syn_crn B)) (.classEq (syn_crn (syn_ccom A B)) (syn_crn A)) p0000 p0005 p0011
  exact p0012

noncomputable def g_res0
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cres A (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres A (syn_c0))))
  have p0001 :=
    @g_xp0r (syn_cvv)
  have p0002 :=
    @g_ineq2i (syn_cxp (syn_c0) (syn_cvv)) (syn_c0) A p0001
  have p0003 :=
    @g_in0 A
  have p0004 :=
    @g_n_3eqtri (syn_cres A (syn_c0)) (syn_cin A (syn_cxp (syn_c0) (syn_cvv))) (syn_cin A (syn_c0)) (syn_c0) p0000 p0002 p0003
  exact p0004

noncomputable def g_resundi
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cres A (syn_cun B C)) (syn_cun (syn_cres A B) (syn_cres A C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_xpundir B C (syn_cvv)
  have p0001 :=
    @g_ineq2i (syn_cxp (syn_cun B C) (syn_cvv)) (syn_cun (syn_cxp B (syn_cvv)) (syn_cxp C (syn_cvv))) A p0000
  have p0002 :=
    @g_indi A (syn_cxp B (syn_cvv)) (syn_cxp C (syn_cvv))
  have p0003 :=
    @g_eqtri (syn_cin A (syn_cxp (syn_cun B C) (syn_cvv))) (syn_cin A (syn_cun (syn_cxp B (syn_cvv)) (syn_cxp C (syn_cvv)))) (syn_cun (syn_cin A (syn_cxp B (syn_cvv))) (syn_cin A (syn_cxp C (syn_cvv)))) p0001 p0002
  have p0004 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres A (syn_cun B C))))
  have p0005 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres A B)))
  have p0006 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres A C)))
  have p0007 :=
    @g_uneq12i (syn_cres A B) (syn_cin A (syn_cxp B (syn_cvv))) (syn_cres A C) (syn_cin A (syn_cxp C (syn_cvv))) p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_cin A (syn_cxp (syn_cun B C) (syn_cvv))) (syn_cun (syn_cin A (syn_cxp B (syn_cvv))) (syn_cin A (syn_cxp C (syn_cvv)))) (syn_cres A (syn_cun B C)) (syn_cun (syn_cres A B) (syn_cres A C)) p0003 p0004 p0007
  exact p0008

noncomputable def g_resundir
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cres (syn_cun A B) C) (syn_cun (syn_cres A C) (syn_cres B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_indir A B (syn_cxp C (syn_cvv))
  have p0001 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres (syn_cun A B) C)))
  have p0002 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres A C)))
  have p0003 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres B C)))
  have p0004 :=
    @g_uneq12i (syn_cres A C) (syn_cin A (syn_cxp C (syn_cvv))) (syn_cres B C) (syn_cin B (syn_cxp C (syn_cvv))) p0002 p0003
  have p0005 :=
    @g_n_3eqtr4i (syn_cin (syn_cun A B) (syn_cxp C (syn_cvv))) (syn_cun (syn_cin A (syn_cxp C (syn_cvv))) (syn_cin B (syn_cxp C (syn_cvv)))) (syn_cres (syn_cun A B) C) (syn_cun (syn_cres A C) (syn_cres B C)) p0000 p0001 p0004
  exact p0005

noncomputable def g_dmres
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cres A B)) (syn_cin B (syn_cdm A))) := by
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
  have dv_cache_0001 : y ∉ ((Wff.classMem (.cv x) B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cres A B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cdm A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cdm (syn_cres A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_19_41v (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) B) y dv_cache_0001
  have p0001 :=
    @g_eldm y (.cv x) (syn_cres A B) dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_brres (.cv x) (.cv y) A B
  have p0003 :=
    @g_exbii (syn_wbr (.cv x) (syn_cres A B) (.cv y)) (syn_wa (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) B)) y p0002
  have p0004 :=
    @g_bitri (.classMem (.cv x) (syn_cdm (syn_cres A B))) (syn_wex y (syn_wbr (.cv x) (syn_cres A B) (.cv y))) (syn_wex y (syn_wa (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) B))) p0001 p0003
  have p0005 :=
    @g_eldm y (.cv x) A dv_cache_0002 dv_cache_0004
  have p0006 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdm A)) (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) B) p0005
  have p0007 :=
    @g_n_3bitr4ri (syn_wex y (syn_wa (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) B))) (syn_wa (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) B)) (.classMem (.cv x) (syn_cdm (syn_cres A B))) (syn_wa (.classMem (.cv x) (syn_cdm A)) (.classMem (.cv x) B)) p0000 p0004 p0006
  have p0008 :=
    @g_ineqri x (syn_cdm A) B (syn_cdm (syn_cres A B)) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0007
  have p0009 :=
    @g_incom (syn_cdm A) B
  have p0010 :=
    @g_eqtr3i (syn_cin (syn_cdm A) B) (syn_cdm (syn_cres A B)) (syn_cin B (syn_cdm A)) p0008 p0009
  exact p0010

noncomputable def g_ssdmres
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_cdm B)) (.classEq (syn_cdm (syn_cres B A)) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wss] using (Nominal.biimpRefl (syn_wss A (syn_cdm B))))
  have p0001 :=
    @g_dmres B A
  have p0002 :=
    @g_eqeq1i (syn_cdm (syn_cres B A)) (syn_cin A (syn_cdm B)) A p0001
  have p0003 :=
    @g_bitr4i (syn_wss A (syn_cdm B)) (.classEq (syn_cin A (syn_cdm B)) A) (.classEq (syn_cdm (syn_cres B A)) A) p0000 p0002
  exact p0003

noncomputable def g_resss
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cres A B) A) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres A B)))
  have p0001 :=
    @g_inss1 A (syn_cxp B (syn_cvv))
  have p0002 :=
    @g_eqsstri (syn_cres A B) (syn_cin A (syn_cxp B (syn_cvv))) A p0000 p0001
  exact p0002

noncomputable def g_ssres2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cres C A) (syn_cres C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_xpss1 A B (syn_cvv)
  have p0001 :=
    @g_sslin (syn_cxp A (syn_cvv)) (syn_cxp B (syn_cvv)) C
  have p0002 :=
    @g_syl (syn_wss A B) (syn_wss (syn_cxp A (syn_cvv)) (syn_cxp B (syn_cvv))) (syn_wss (syn_cin C (syn_cxp A (syn_cvv))) (syn_cin C (syn_cxp B (syn_cvv)))) p0000 p0001
  have p0003 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres C A)))
  have p0004 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres C B)))
  have p0005 :=
    @g_n_3sstr4g (syn_wss A B) (syn_cin C (syn_cxp A (syn_cvv))) (syn_cin C (syn_cxp B (syn_cvv))) (syn_cres C A) (syn_cres C B) p0002 p0003 p0004
  exact p0005

noncomputable def g_ssreseq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss (syn_cdm A) B) (.classEq (syn_cres A B) A)) := by
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
  have dv_cache_0003 : x ∉ ((syn_cres A B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cres A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wss (syn_cdm A) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wss (syn_cdm A) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_resss A B
  have p0001 :=
    @g_a1i (syn_wss (syn_cres A B) A) (syn_wss (syn_cdm A) B) p0000
  have p0002 :=
    @g_opeldm (.cv x) (.cv y) A
  have p0003 :=
    @g_ssel (syn_cdm A) B (.cv x)
  have p0004 :=
    @g_syl5 (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (.cv x) (syn_cdm A)) (syn_wss (syn_cdm A) B) (.classMem (.cv x) B) p0002 p0003
  have p0005 :=
    @g_ancld (syn_wss (syn_cdm A) B) (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (.cv x) B) p0004
  have p0006 :=
    @g_opelres (.cv x) (.cv y) A B
  have p0007 :=
    @g_syl6ibr (syn_wss (syn_cdm A) B) (.classMem (syn_cop (.cv x) (.cv y)) A) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (.cv x) B)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cres A B)) p0005 p0006
  have p0008 :=
    @g_relssdv (syn_wss (syn_cdm A) B) x y A (syn_cres A B) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0007
  have p0009 :=
    @g_eqssd (syn_wss (syn_cdm A) B) (syn_cres A B) A p0001 p0008
  exact p0009

noncomputable def g_resopab
    (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cres (syn_copab x y ph) A) (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
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
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres (syn_copab x y ph) A)))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002 :=
    @g_vex y
  have p0003 :=
    @g_biantru (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_opabbii (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cvv))) x y p0003
  have p0005 :=
    @g_eqtr4i (syn_cxp A (syn_cvv)) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cvv)))) (syn_copab x y (.classMem (.cv x) A)) p0001 p0004
  have p0006 :=
    @g_ineq2i (syn_cxp A (syn_cvv)) (syn_copab x y (.classMem (.cv x) A)) (syn_copab x y ph) p0005
  have p0007 :=
    @g_incom (syn_copab x y ph) (syn_copab x y (.classMem (.cv x) A))
  have p0008 :=
    @g_eqtri (syn_cin (syn_copab x y ph) (syn_cxp A (syn_cvv))) (syn_cin (syn_copab x y ph) (syn_copab x y (.classMem (.cv x) A))) (syn_cin (syn_copab x y (.classMem (.cv x) A)) (syn_copab x y ph)) p0006 p0007
  have p0009 :=
    @g_inopab (.classMem (.cv x) A) ph x y dv_cache_0005
  have p0010 :=
    @g_n_3eqtri (syn_cres (syn_copab x y ph) A) (syn_cin (syn_copab x y ph) (syn_cxp A (syn_cvv))) (syn_cin (syn_copab x y (.classMem (.cv x) A)) (syn_copab x y ph)) (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) p0000 p0008 p0009
  exact p0010

noncomputable def g_iss
    (A : Class) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_cid)) (.classEq A (syn_cres (syn_cid) (syn_cdm A)))) := by
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
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classMem (syn_cop (.cv x) (.cv x)) A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_wss A (syn_cid))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cres (syn_cid) (syn_cdm A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cres (syn_cid) (syn_cdm A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_wss A (syn_cid))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_ssel A (syn_cid) (syn_cop (.cv x) (.cv y))
  have p0001 :=
    @g_opeldm (.cv x) (.cv y) A
  have p0002 :=
    @g_a1i (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (.cv x) (syn_cdm A))) (syn_wss A (syn_cid)) p0001
  have p0003 :=
    @g_jcad (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classMem (.cv x) (syn_cdm A)) p0000 p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv y))))
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_ideq (.cv x) (.cv y) p0005
  have p0007_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cid syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0007 :=
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y) p0004 p0007_e01_recanon
  have p0008 :=
    @g_anbi1i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.objEq x y) (.classMem (.cv x) (syn_cdm A)) p0007
  have p0009 :=
    @g_eldm2 y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0010 :=
    @g_syl6ib (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.objEq x y) p0000 p0007
  have p0011 :=
    @g_opeq2 (.cv x) (.cv y) (.cv x)
  have p0012_e00_recanon : Nominal.NPrf (.imp (.objEq x y) (.classEq (syn_cop (.cv x) (.cv x)) (syn_cop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0011
  have p0012 :=
    @g_eleq1d (.objEq x y) (syn_cop (.cv x) (.cv x)) (syn_cop (.cv x) (.cv y)) A p0012_e00_recanon
  have p0013 :=
    @g_biimprd (.objEq x y) (.classMem (syn_cop (.cv x) (.cv x)) A) (.classMem (syn_cop (.cv x) (.cv y)) A) p0012
  have p0014 :=
    @g_syli (.classMem (syn_cop (.cv x) (.cv y)) A) (syn_wss A (syn_cid)) (.objEq x y) (.classMem (syn_cop (.cv x) (.cv x)) A) p0010 p0013
  have p0015 :=
    @g_exlimdv (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv x)) A) y dv_cache_0003 dv_cache_0004 p0014
  have p0016 :=
    @g_syl5bi (.classMem (.cv x) (syn_cdm A)) (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)) (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv x)) A) p0009 p0015
  have p0017 :=
    @g_biimpd (.objEq x y) (.classMem (syn_cop (.cv x) (.cv x)) A) (.classMem (syn_cop (.cv x) (.cv y)) A) p0012
  have p0018 :=
    @g_syl9 (syn_wss A (syn_cid)) (.classMem (.cv x) (syn_cdm A)) (.classMem (syn_cop (.cv x) (.cv x)) A) (.objEq x y) (.classMem (syn_cop (.cv x) (.cv y)) A) p0016 p0017
  have p0019 :=
    @g_imp3a (syn_wss A (syn_cid)) (.objEq x y) (.classMem (.cv x) (syn_cdm A)) (.classMem (syn_cop (.cv x) (.cv y)) A) p0018
  have p0020 :=
    @g_syl5bi (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classMem (.cv x) (syn_cdm A))) (syn_wa (.objEq x y) (.classMem (.cv x) (syn_cdm A))) (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A) p0008 p0019
  have p0021 :=
    @g_impbid (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classMem (.cv x) (syn_cdm A))) p0003 p0020
  have p0022 :=
    @g_opelres (.cv x) (.cv y) (syn_cid) (syn_cdm A)
  have p0023 :=
    @g_syl6bbr (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classMem (.cv x) (syn_cdm A))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cres (syn_cid) (syn_cdm A))) p0021 p0022
  have p0024 :=
    @g_eqrelrdv (syn_wss A (syn_cid)) x y A (syn_cres (syn_cid) (syn_cdm A)) dv_cache_0005 dv_cache_0002 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0004 dv_cache_0009 p0023
  have p0025 :=
    @g_resss (syn_cid) (syn_cdm A)
  have p0026 :=
    @g_sseq1 A (syn_cres (syn_cid) (syn_cdm A)) (syn_cid)
  have p0027 :=
    @g_mpbiri (.classEq A (syn_cres (syn_cid) (syn_cdm A))) (syn_wss A (syn_cid)) (syn_wss (syn_cres (syn_cid) (syn_cdm A)) (syn_cid)) p0025 p0026
  have p0028 :=
    @g_impbii (syn_wss A (syn_cid)) (.classEq A (syn_cres (syn_cid) (syn_cdm A))) p0024 p0027
  exact p0028

noncomputable def g_resopab2
    (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wss A B) (.classEq (syn_cres (syn_copab x y (syn_wa (.classMem (.cv x) B) ph)) A) (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
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
  have dv_cache_0004 : x ∉ ((syn_wss A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_wss A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_resopab (syn_wa (.classMem (.cv x) B) ph) x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_ssel A B (.cv x)
  have p0002 :=
    @g_pm4_71 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0003 :=
    @g_sylib (syn_wss A B) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B)) (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))) p0001 p0002
  have p0004 :=
    @g_anbi1d (syn_wss A B) (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) ph p0003
  have p0005 :=
    @g_anass (.classMem (.cv x) A) (.classMem (.cv x) B) ph
  have p0006 :=
    @g_syl6rbb (syn_wss A B) (syn_wa (.classMem (.cv x) A) ph) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) ph) (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) ph)) p0004 p0005
  have p0007 :=
    @g_opabbidv (syn_wss A B) (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) ph)) (syn_wa (.classMem (.cv x) A) ph) x y dv_cache_0004 dv_cache_0005 p0006
  have p0008 :=
    @g_syl5eq (syn_wss A B) (syn_cres (syn_copab x y (syn_wa (.classMem (.cv x) B) ph)) A) (syn_copab x y (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) ph))) (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) p0000 p0007
  exact p0008

noncomputable def g_dmresi
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cres (syn_cid) A)) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ssv A
  have p0001 :=
    @g_dmi
  have p0002 :=
    @g_sseqtr4i A (syn_cvv) (syn_cdm (syn_cid)) p0000 p0001
  have p0003 :=
    @g_ssdmres A (syn_cid)
  have p0004 :=
    @g_mpbi (syn_wss A (syn_cdm (syn_cid))) (.classEq (syn_cdm (syn_cres (syn_cid) A)) A) p0002 p0003
  exact p0004

noncomputable def g_resid
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cres A (syn_cvv)) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_ssv (syn_cdm A)
  have p0001 :=
    @g_ssreseq A (syn_cvv)
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

#print axioms g_resid

end NFChoice.DirectNominalPrf.WPPReplay
