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
import NominalAlphaRepairedBase001049OprabReflected001
import NominalAlphaPrefix050WppNotmem014Data
import NominalAlphaGlobal051ProofData001
import NominalAlphaRelease004Coarse052
import NominalAlphaRelease004Coarse053
import NominalAlphaRelease004Coarse054
import NominalAlphaRelease004Coarse055
import NominalAlphaRelease004Coarse056
import NominalAlphaRelease004Coarse057
import NominalAlphaRelease004Coarse058
import NominalAlphaRelease004Coarse059
import NominalAlphaRelease004Coarse060
import NominalAlphaRelease004Coarse061
import NominalAlphaRelease004Coarse062
import NominalAlphaRelease004Coarse063
import NominalAlphaRelease004Coarse064
import NominalAlphaRelease004Coarse065
import NominalAlphaRelease004Coarse066
import NominalAlphaRelease004Coarse067
import NominalAlphaRelease004Coarse068
import NominalAlphaRelease004Coarse069
import NominalAlphaRelease004Coarse070
import NominalAlphaRelease004Coarse071
import NominalAlphaRelease004Coarse072
import NominalAlphaRelease004Coarse073
import NominalAlphaRelease004Coarse074
import NominalAlphaRelease004Coarse075
import NominalAlphaRelease004Coarse076
import NominalAlphaRelease004Coarse077
import NominalAlphaRelease004Coarse078
import NominalAlphaRelease004Coarse079
import NominalAlphaRelease004Coarse080
import NominalAlphaRelease004Coarse081
import NominalAlphaRelease004Coarse082
import NominalAlphaRelease004Coarse083
import NominalAlphaRelease004Coarse084
import NominalAlphaRelease004Coarse085
import NominalAlphaRelease004Coarse086
import NominalAlphaRelease004Coarse087
import NominalAlphaHygieneV5Probe088
import NominalAlphaRelease004Coarse089
import NominalAlphaRelease004Coarse090
import NominalAlphaHygieneV5Coalesced091B
import NominalAlphaHygieneV5Coalesced092
import NominalAlphaHygieneV5Coalesced093
import NominalAlphaHygieneV5Coalesced094
import NominalAlphaHygieneV5Coalesced095
import NominalAlphaHygieneV5Coalesced096
import NominalAlphaHygieneV5Coalesced097
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk016Compact001

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

noncomputable def g_sifrreflectndv
    (D : Class) (R : Class) (hyp_sifrreflectndv_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_sifrreflectndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cfound) D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let r : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_r : x ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_r : z ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_r_ne_z : r ≠ z :=
    Ne.symm fresh_z_ne_r
  have fresh_z_ne_q : z ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_y_ne_r : y ≠ r := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_y_ne_q : y ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_r_ne_q : r ≠ q := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_r : q ≠ r :=
    Ne.symm fresh_r_ne_q
  have dv_cache_0001 : q ∉ ((syn_csi R)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_cpw1 (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0006 : r ∉ ((syn_csn (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((Wff.imp (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) (.classEq (syn_csn (.cv z)) (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_z, fresh_r_ne_q, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_x, fresh_z_ne_q, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Wff.classEq (.cv y) (syn_cuni (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cuni (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (syn_cuni (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_ne_q, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_z, fresh_q_ne_y, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : q ∉ ((syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, fresh_q_not_D, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0023 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0024 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have p0000 :=
    @g_a1i (.classMem R (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_sifrreflectndv_1
  have p0001 :=
    @g_a1i (.classMem D (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) hyp_sifrreflectndv_2
  have p0002 :=
    @g_simpl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))
  have p0003 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0004 :=
    @g_breqi (syn_csi R) (syn_cpw1 D) (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0003
  have p0005 :=
    @g_brin (syn_csi R) (syn_cpw1 D) (syn_cstrict) (syn_cfound)
  have p0006 :=
    @g_bitri (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cin (syn_cstrict) (syn_cfound)) (syn_cpw1 D)) (syn_wa (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D))) p0004 p0005
  have p0007 :=
    @g_simprbi (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)) p0006
  have p0008 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)) p0002 p0007
  have p0009 :=
    @g_vex x
  have p0010 :=
    @g_pw1ex (.cv x) p0009
  have p0011 :=
    @g_a1i (.classMem (syn_cpw1 (.cv x)) (syn_cvv)) (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) p0010
  have p0012 :=
    @g_simpr (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))
  have p0013 :=
    @g_simpl (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))
  have p0014 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) D) p0012 p0013
  have p0015 :=
    @g_pw1ss (.cv x) D
  have p0016 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) D) (syn_wss (syn_cpw1 (.cv x)) (syn_cpw1 D)) p0014 p0015
  have p0017 :=
    @g_simpr (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))
  have p0018 :=
    @g_simpr (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))
  have p0019 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0))) (syn_wne (.cv x) (syn_c0)) p0017 p0018
  have p0020 :=
    @g_pw10b (.cv x)
  have p0021 :=
    @g_necon3bii (syn_cpw1 (.cv x)) (syn_c0) (.cv x) (syn_c0) p0020
  have p0022 :=
    @g_biimpri (syn_wne (syn_cpw1 (.cv x)) (syn_c0)) (syn_wne (.cv x) (syn_c0)) p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_cpw1 (.cv x)) (syn_c0)) p0019 p0022
  have p0024 :=
    @g_frd (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) q r (syn_cpw1 D) (syn_csi R) (syn_cvv) (syn_cpw1 (.cv x)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0008 p0011 p0016 p0023
  have p0025 :=
    @g_simpr (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0026 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))) (.classMem (.cv q) (syn_cpw1 (.cv x))) p0025 p0026
  have p0028 :=
    @g_hnwpw1argcl (.cv x) q
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0027 p0028
  have p0030 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (.cv x)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (.cv x)) p0029 p0030
  have p0032 :=
    @g_vex z
  have p0033 :=
    @g_vex q
  have p0034 :=
    @g_uniex (.cv q) p0033
  have p0035 :=
    @g_brsnsi (.cv z) (syn_cuni (.cv q)) R p0032 p0034
  have p0036 :=
    @g_biimpri (syn_wbr (syn_csn (.cv z)) (syn_csi R) (syn_csn (syn_cuni (.cv q)))) (syn_wbr (.cv z) R (syn_cuni (.cv q))) p0035
  have p0037 :=
    @g_a1i (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (syn_wbr (syn_csn (.cv z)) (syn_csi R) (syn_csn (syn_cuni (.cv q))))) (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) p0036
  have p0038 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))
  have p0039 :=
    @g_simpr (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0040 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))) (.classMem (.cv q) (syn_cpw1 (.cv x))) p0039 p0040
  have p0042 :=
    @g_hnwpw1argcl (.cv x) q
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0041 p0042
  have p0044 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (.cv x)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0043 p0044
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0038 p0045
  have p0047 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (.cv q) (syn_csn (syn_cuni (.cv q))) p0046
  have p0048 :=
    @g_breq2d (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_csn (syn_cuni (.cv q))) (.cv q) (syn_csn (.cv z)) (syn_csi R) p0047
  have p0049 :=
    @g_biimpd (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (syn_csn (.cv z)) (syn_csi R) (syn_csn (syn_cuni (.cv q)))) (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) p0048
  have p0050 :=
    @g_syld (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) R (syn_cuni (.cv q))) (syn_wbr (syn_csn (.cv z)) (syn_csi R) (syn_csn (syn_cuni (.cv q)))) (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) p0037 p0049
  have p0051 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))
  have p0052 :=
    @g_simpr (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0053 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0054 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))) p0052 p0053
  have p0055 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))) p0051 p0054
  have p0056 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))
  have p0057 :=
    @g_snelpw1 (.cv z) (.cv x)
  have p0058 :=
    @g_biimpri (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))) (.classMem (.cv z) (.cv x)) p0057
  have p0059 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (.classMem (.cv z) (.cv x)) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))) p0056 p0058
  have p0060 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x))) p0055 p0059
  have p0061 :=
    @g_id (.classEq (.cv r) (syn_csn (.cv z)))
  have p0062 :=
    @g_breq1d (.classEq (.cv r) (syn_csn (.cv z))) (.cv r) (syn_csn (.cv z)) (.cv q) (syn_csi R) p0061
  have p0063 :=
    @g_id (.classEq (.cv r) (syn_csn (.cv z)))
  have p0064 :=
    @g_eqeq1d (.classEq (.cv r) (syn_csn (.cv z))) (.cv r) (syn_csn (.cv z)) (.cv q) p0063
  have p0065 :=
    @g_imbi12d (.classEq (.cv r) (syn_csn (.cv z))) (syn_wbr (.cv r) (syn_csi R) (.cv q)) (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)) (.classEq (syn_csn (.cv z)) (.cv q)) p0062 p0064
  have p0066 :=
    @g_rspccva (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))) (.imp (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) (.classEq (syn_csn (.cv z)) (.cv q))) r (syn_csn (.cv z)) (syn_cpw1 (.cv x)) dv_cache_0006 dv_cache_0004 dv_cache_0007 p0065
  have p0067 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_wa (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv x)))) (.imp (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) (.classEq (syn_csn (.cv z)) (.cv q))) p0060 p0066
  have p0068 :=
    @g_syld (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) R (syn_cuni (.cv q))) (syn_wbr (syn_csn (.cv z)) (syn_csi R) (.cv q)) (.classEq (syn_csn (.cv z)) (.cv q)) p0050 p0067
  have p0069 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (.classEq (syn_csn (.cv z)) (.cv q))
  have p0070 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (.classEq (syn_csn (.cv z)) (.cv q))
  have p0071 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))
  have p0072 :=
    @g_simpr (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))
  have p0073 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q))))) (.classMem (.cv q) (syn_cpw1 (.cv x))) p0072 p0073
  have p0075 :=
    @g_hnwpw1argcl (.cv x) q
  have p0076 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0074 p0075
  have p0077 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (.cv x)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0078 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0076 p0077
  have p0079 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0071 p0078
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (.classEq (syn_csn (.cv z)) (.cv q))) (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0070 p0079
  have p0081 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (.classEq (syn_csn (.cv z)) (.cv q))) (syn_csn (.cv z)) (.cv q) (syn_csn (syn_cuni (.cv q))) p0069 p0080
  have p0082 :=
    @g_vex z
  have p0083 :=
    @g_sneqr (.cv z) (syn_cuni (.cv q)) p0082
  have p0084 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (.classEq (syn_csn (.cv z)) (.cv q))) (.classEq (syn_csn (.cv z)) (syn_csn (syn_cuni (.cv q)))) (.classEq (.cv z) (syn_cuni (.cv q))) p0081 p0083
  have p0085 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (.classEq (syn_csn (.cv z)) (.cv q)) (.classEq (.cv z) (syn_cuni (.cv q))) p0084
  have p0086 :=
    @g_syld (syn_wa (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (syn_csn (.cv z)) (.cv q)) (.classEq (.cv z) (syn_cuni (.cv q))) p0068 p0085
  have p0087 :=
    @g_ralrimiva (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (syn_cuni (.cv q)))) z (.cv x) dv_cache_0008 p0086
  have p0088 :=
    @g_jca (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (.classMem (syn_cuni (.cv q)) (.cv x)) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (syn_cuni (.cv q))))) p0031 p0087
  have p0089 :=
    @g_id (.classEq (.cv y) (syn_cuni (.cv q)))
  have p0090 :=
    @g_breq2d (.classEq (.cv y) (syn_cuni (.cv q))) (.cv y) (syn_cuni (.cv q)) (.cv z) R p0089
  have p0091 :=
    @g_id (.classEq (.cv y) (syn_cuni (.cv q)))
  have p0092 :=
    @g_eqeq2d (.classEq (.cv y) (syn_cuni (.cv q))) (.cv y) (syn_cuni (.cv q)) (.cv z) p0091
  have p0093 :=
    @g_imbi12d (.classEq (.cv y) (syn_cuni (.cv q))) (syn_wbr (.cv z) R (.cv y)) (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (.cv y)) (.classEq (.cv z) (syn_cuni (.cv q))) p0090 p0092
  have p0094 :=
    @g_ralbidv (.classEq (.cv y) (syn_cuni (.cv q))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))) (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (syn_cuni (.cv q)))) z (.cv x) dv_cache_0009 p0093
  have p0095 :=
    @g_rspcev (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (syn_cuni (.cv q))))) y (syn_cuni (.cv q)) (.cv x) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0094
  have p0096 :=
    @g_syl (syn_wa (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (.cv x))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) (syn_wa (.classMem (syn_cuni (.cv q)) (.cv x)) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (syn_cuni (.cv q))) (.classEq (.cv z) (syn_cuni (.cv q)))))) (syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) p0088 p0095
  have p0097_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wrex q (syn_cpw1 (.cv x)) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi syn_csi syn_copab syn_cwe syn_cin syn_cstrict syn_cfound syn_cpw1
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0024
  have p0097 :=
    @g_rexlimddv (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wral r (syn_cpw1 (.cv x)) (.imp (syn_wbr (.cv r) (syn_csi R) (.cv q)) (.classEq (.cv r) (.cv q)))) (syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) q (syn_cpw1 (.cv x)) dv_cache_0013 dv_cache_0014 p0097_e00_recanon p0096
  have p0098_e02_recanon : Nominal.NPrf (.imp (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wss (.cv x) D) (syn_wne (.cv x) (syn_c0)))) (syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi syn_csi syn_copab syn_cwe syn_cin syn_cstrict syn_cfound syn_cpw1
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0097
  have p0098 :=
    @g_frrd (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x z y D R dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0000 p0001 p0098_e02_recanon
  exact p0098

noncomputable def g_siwereflectndv
    (D : Class) (R : Class) (hyp_siwereflectndv_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_siwereflectndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cwe) D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_siorreflectndv D R hyp_siwereflectndv_1 hyp_siwereflectndv_2
  have p0001 :=
    @g_sifrreflectndv D R hyp_siwereflectndv_1 hyp_siwereflectndv_2
  have p0002 :=
    @g_jca (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0000 p0001
  have p0003 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0004 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0003
  have p0005 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0006 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0004 p0005
  have p0007 :=
    @g_biimpri (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0006
  have p0008 :=
    @g_syl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) (syn_wbr R (syn_cwe) D) p0002 p0007
  exact p0008

noncomputable def g_hndownbrclndv
    (x : Var) (y : Var) (S : Class) (a : Var) (b : Var) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv b)) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ S.fv ∪ ({a} : Finset Var) ∪ ({b} : Finset Var)
  have dv_cache_0001 : x ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_b_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_b_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_x), (Ne.symm dv_b_x), dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_y), (Ne.symm dv_b_y), dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_vex a
  have p0001 :=
    @g_vex b
  have p0002 :=
    @g_id (.classEq (.cv x) (.cv a))
  have p0003 :=
    @g_sneqd (.classEq (.cv x) (.cv a)) (.cv x) (.cv a) p0002
  have p0004 :=
    @g_breq1d (.classEq (.cv x) (.cv a)) (syn_csn (.cv x)) (syn_csn (.cv a)) (syn_csn (.cv y)) S p0003
  have p0005 :=
    @g_id (.classEq (.cv y) (.cv b))
  have p0006 :=
    @g_sneqd (.classEq (.cv y) (.cv b)) (.cv y) (.cv b) p0005
  have p0007 :=
    @g_breq2d (.classEq (.cv y) (.cv b)) (syn_csn (.cv y)) (syn_csn (.cv b)) (syn_csn (.cv a)) S p0006
  have p0008 :=
    @g_eqid (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
  have p0009 :=
    @g_brab (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv a)) S (syn_csn (.cv b))) x y (.cv a) (.cv b) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0001 p0004 p0007 p0008
  exact p0009

#print axioms g_hndownbrclndv

end NFChoice.DirectNominalPrf.WPPReplay
