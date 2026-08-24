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
import NominalWPPReplayChunk016Compact001Part025

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

noncomputable def g_sifrndv
    (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) D) (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let v : Var := freshVar proofSupport 3
  let u : Var := freshVar proofSupport 4
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
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_v : x ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_v : z ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_y_ne_v : y ≠ v := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_v_ne_u : v ≠ u := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have dv_cache_0001 : u ∉ (R).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_cuni (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((syn_cuni (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0006 : v ∉ ((syn_cuni (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((Wff.imp (syn_wbr (syn_cuni (.cv z)) R (.cv u)) (.classEq (syn_cuni (.cv z)) (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_z, fresh_v_ne_u, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_x, fresh_z_ne_u, fresh_z_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Wff.classEq (.cv y) (syn_csn (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_csn (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (syn_csn (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_ne_u, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : u ∉ ((syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.classEq (.cv z) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_z, fresh_u_ne_y, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : u ∉ ((syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, fresh_u_not_D, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
    @g_brex R D (syn_cwe)
  have p0001 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0000
  have p0002 :=
    @g_siexg R (syn_cvv)
  have p0003 :=
    @g_syl (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem (syn_csi R) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_brex R D (syn_cwe)
  have p0005 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0004
  have p0006 :=
    @g_pw1exg D (syn_cvv)
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) D) (.classMem D (syn_cvv)) (.classMem (syn_cpw1 D) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0009 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0010 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0009
  have p0011 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0012 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0010 p0011
  have p0013 :=
    @g_simprbi (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cfound) D) p0008 p0013
  have p0015 :=
    @g_vex x
  have p0016 :=
    @g_uniex (.cv x) p0015
  have p0017 :=
    @g_a1i (.classMem (syn_cuni (.cv x)) (syn_cvv)) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) p0016
  have p0018 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0019 :=
    @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0020 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) (syn_cpw1 D)) p0018 p0019
  have p0021 :=
    @g_pw1subuniss x D
  have p0022 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) (syn_cpw1 D)) (syn_wss (syn_cuni (.cv x)) D) p0020 p0021
  have p0023 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0024 :=
    @g_pw1subunine x D
  have p0025 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))) (syn_wne (syn_cuni (.cv x)) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_frd (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) u v D R (syn_cvv) (syn_cuni (.cv x)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0014 p0017 p0022 p0025
  have p0027 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0028 :=
    @g_simpl (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))) (.classMem (.cv u) (syn_cuni (.cv x))) p0027 p0028
  have p0030 :=
    @g_snelpw1 (.cv u) (syn_cuni (.cv x))
  have p0031 :=
    @g_biimpri (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_cuni (.cv x)))) (.classMem (.cv u) (syn_cuni (.cv x))) p0030
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv u) (syn_cuni (.cv x))) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_cuni (.cv x)))) p0029 p0031
  have p0033 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0034 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0035 :=
    @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0036 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) (syn_cpw1 D)) p0034 p0035
  have p0037 :=
    @g_pw1ss1c D
  have p0038 :=
    @g_a1i (syn_wss (syn_cpw1 D) (syn_c1c)) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) p0037
  have p0039 :=
    @g_sstrd (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (.cv x) (syn_cpw1 D) (syn_c1c) p0036 p0038
  have p0040 :=
    @g_eqpw1uni (.cv x)
  have p0041 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) (syn_c1c)) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0039 p0040
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0033 p0041
  have p0043 :=
    @g_eleqtrrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (syn_csn (.cv u)) (syn_cpw1 (syn_cuni (.cv x))) (.cv x) p0032 p0042
  have p0044 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0045 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))
  have p0046 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))
  have p0047 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0048 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0049 :=
    @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0050 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) (syn_cpw1 D)) p0048 p0049
  have p0051 :=
    @g_pw1ss1c D
  have p0052 :=
    @g_a1i (syn_wss (syn_cpw1 D) (syn_c1c)) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) p0051
  have p0053 :=
    @g_sstrd (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (.cv x) (syn_cpw1 D) (syn_c1c) p0050 p0052
  have p0054 :=
    @g_eqpw1uni (.cv x)
  have p0055 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) (syn_c1c)) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0053 p0054
  have p0056 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0047 p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0046 p0056
  have p0058 :=
    @g_eleqtrd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.cv z) (.cv x) (syn_cpw1 (syn_cuni (.cv x))) p0045 p0057
  have p0059 :=
    @g_hnwpw1argcl (syn_cuni (.cv x)) z
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.classMem (.cv z) (syn_cpw1 (syn_cuni (.cv x)))) (syn_wa (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z))))) p0058 p0059
  have p0061 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0060
  have p0062 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0044 p0061
  have p0063 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0064 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0065 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))
  have p0066 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))
  have p0067 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0068 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0069 :=
    @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0070 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) (syn_cpw1 D)) p0068 p0069
  have p0071 :=
    @g_pw1ss1c D
  have p0072 :=
    @g_a1i (syn_wss (syn_cpw1 D) (syn_c1c)) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) p0071
  have p0073 :=
    @g_sstrd (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (.cv x) (syn_cpw1 D) (syn_c1c) p0070 p0072
  have p0074 :=
    @g_eqpw1uni (.cv x)
  have p0075 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) (syn_c1c)) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0073 p0074
  have p0076 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0067 p0075
  have p0077 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0066 p0076
  have p0078 :=
    @g_eleqtrd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.cv z) (.cv x) (syn_cpw1 (syn_cuni (.cv x))) p0065 p0077
  have p0079 :=
    @g_hnwpw1argcl (syn_cuni (.cv x)) z
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.classMem (.cv z) (syn_cpw1 (syn_cuni (.cv x)))) (syn_wa (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z))))) p0078 p0079
  have p0081 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0080
  have p0082 :=
    @g_breq1d (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.cv z) (syn_csn (syn_cuni (.cv z))) (syn_csn (.cv u)) (syn_csi R) p0081
  have p0083 :=
    @g_vex z
  have p0084 :=
    @g_uniex (.cv z) p0083
  have p0085 :=
    @g_vex u
  have p0086 :=
    @g_brsnsi (syn_cuni (.cv z)) (.cv u) R p0084 p0085
  have p0087 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv z))) (syn_csi R) (syn_csn (.cv u))) (syn_wbr (syn_cuni (.cv z)) R (.cv u))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) p0086
  have p0088 :=
    @g_bitrd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (syn_wbr (syn_csn (syn_cuni (.cv z))) (syn_csi R) (syn_csn (.cv u))) (syn_wbr (syn_cuni (.cv z)) R (.cv u)) p0082 p0087
  have p0089 :=
    @g_biimpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (syn_wbr (syn_cuni (.cv z)) R (.cv u)) p0088
  have p0090 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (syn_wbr (syn_cuni (.cv z)) R (.cv u))) p0064 p0089
  have p0091 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (syn_wbr (syn_cuni (.cv z)) R (.cv u)) p0063 p0090
  have p0092 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0093 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))
  have p0094 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) p0092 p0093
  have p0095 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0096 :=
    @g_simpr (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))) p0095 p0096
  have p0098 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))) p0094 p0097
  have p0099 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0100 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))
  have p0101 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))
  have p0102 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0103 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0104 :=
    @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0105 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) (syn_cpw1 D)) p0103 p0104
  have p0106 :=
    @g_pw1ss1c D
  have p0107 :=
    @g_a1i (syn_wss (syn_cpw1 D) (syn_c1c)) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) p0106
  have p0108 :=
    @g_sstrd (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (.cv x) (syn_cpw1 D) (syn_c1c) p0105 p0107
  have p0109 :=
    @g_eqpw1uni (.cv x)
  have p0110 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) (syn_c1c)) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0108 p0109
  have p0111 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0102 p0110
  have p0112 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0101 p0111
  have p0113 :=
    @g_eleqtrd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.cv z) (.cv x) (syn_cpw1 (syn_cuni (.cv x))) p0100 p0112
  have p0114 :=
    @g_hnwpw1argcl (syn_cuni (.cv x)) z
  have p0115 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.classMem (.cv z) (syn_cpw1 (syn_cuni (.cv x)))) (syn_wa (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z))))) p0113 p0114
  have p0116 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0115
  have p0117 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) p0099 p0116
  have p0118 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))) (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) p0098 p0117
  have p0119 :=
    @g_breq1 (.cv v) (syn_cuni (.cv z)) (.cv u) R
  have p0120 :=
    @g_eqeq1 (.cv v) (syn_cuni (.cv z)) (.cv u)
  have p0121 :=
    @g_imbi12d (.classEq (.cv v) (syn_cuni (.cv z))) (syn_wbr (.cv v) R (.cv u)) (syn_wbr (syn_cuni (.cv z)) R (.cv u)) (.classEq (.cv v) (.cv u)) (.classEq (syn_cuni (.cv z)) (.cv u)) p0119 p0120
  have p0122 :=
    @g_rspccva (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))) (.imp (syn_wbr (syn_cuni (.cv z)) R (.cv u)) (.classEq (syn_cuni (.cv z)) (.cv u))) v (syn_cuni (.cv z)) (syn_cuni (.cv x)) dv_cache_0006 dv_cache_0004 dv_cache_0007 p0121
  have p0123 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_wa (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))) (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x)))) (.imp (syn_wbr (syn_cuni (.cv z)) R (.cv u)) (.classEq (syn_cuni (.cv z)) (.cv u))) p0118 p0122
  have p0124 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_wbr (syn_cuni (.cv z)) R (.cv u)) (.classEq (syn_cuni (.cv z)) (.cv u)) p0091 p0123
  have p0125 :=
    @g_sneqd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (syn_cuni (.cv z)) (.cv u) p0124
  have p0126 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))) (.cv z) (syn_csn (syn_cuni (.cv z))) (syn_csn (.cv u)) p0062 p0125
  have p0127 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (syn_csn (.cv u))) p0126
  have p0128 :=
    @g_ralrimiva (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (syn_csn (.cv u)))) z (.cv x) dv_cache_0008 p0127
  have p0129 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (.classMem (syn_csn (.cv u)) (.cv x)) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (syn_csn (.cv u))))) p0043 p0128
  have p0130 :=
    @g_breq2 (.cv y) (syn_csn (.cv u)) (.cv z) (syn_csi R)
  have p0131 :=
    @g_eqeq2 (.cv y) (syn_csn (.cv u)) (.cv z)
  have p0132 :=
    @g_imbi12d (.classEq (.cv y) (syn_csn (.cv u))) (syn_wbr (.cv z) (syn_csi R) (.cv y)) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (.cv y)) (.classEq (.cv z) (syn_csn (.cv u))) p0130 p0131
  have p0133 :=
    @g_ralbidv (.classEq (.cv y) (syn_csn (.cv u))) (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.classEq (.cv z) (.cv y))) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (syn_csn (.cv u)))) z (.cv x) dv_cache_0009 p0132
  have p0134 :=
    @g_rspcev (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.classEq (.cv z) (.cv y)))) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (syn_csn (.cv u))))) y (syn_csn (.cv u)) (.cv x) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0133
  have p0135 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) (syn_wa (.classMem (syn_csn (.cv u)) (.cv x)) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (syn_csn (.cv u)))))) (syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.classEq (.cv z) (.cv y))))) p0129 p0134
  have p0136_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wrex u (syn_cuni (.cv x)) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi syn_cwe syn_cin syn_cstrict syn_cfound syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
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
      p0026
  have p0136 :=
    @g_rexlimddv (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wral v (syn_cuni (.cv x)) (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))) (syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.classEq (.cv z) (.cv y))))) u (syn_cuni (.cv x)) dv_cache_0013 dv_cache_0014 p0136_e00_recanon p0135
  have p0137_e02_recanon : Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))) (syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi syn_cwe syn_cin syn_cstrict syn_cfound syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0136
  have p0137 :=
    @g_frrd (syn_wbr R (syn_cwe) D) x z y (syn_cpw1 D) (syn_csi R) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0003 p0007 p0137_e02_recanon
  exact p0137

#print axioms g_sifrndv

end NFChoice.DirectNominalPrf.WPPReplay
