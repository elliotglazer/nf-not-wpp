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
import NominalWPPReplayChunk012BCompact001Part005

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

noncomputable def g_f1oiso
    (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_H_w : w ∉ H.fv) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) (dv_H_z : z ∉ H.fv) (dv_R_w : w ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1o H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))) (syn_wiso H R S A B)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ({w} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ H.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_v_ne_z : v ≠ z := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_v : z ≠ v :=
    Ne.symm fresh_v_ne_z
  have fresh_v_ne_w : v ≠ w := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_w_ne_v : w ≠ v :=
    Ne.symm fresh_v_ne_w
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_H : v ∉ H.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_u : z ≠ u :=
    Ne.symm fresh_u_ne_z
  have fresh_u_ne_w : u ≠ w := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_w_ne_u : w ≠ u :=
    Ne.symm fresh_u_ne_w
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_H : u ∉ H.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v_ne_u : v ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv z) (syn_cfv H (.cv v)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_z, fresh_x_ne_v, dv_H_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (syn_cfv H (.cv v)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_y_z, fresh_y_ne_v, dv_H_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv w) (syn_cfv H (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_w_x), fresh_x_ne_u, dv_H_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv w) (syn_cfv H (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_w_y), fresh_y_ne_u, dv_H_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cfv H (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_v, dv_H_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_cfv H (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_v, dv_H_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cfv H (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_u, dv_H_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((syn_cfv H (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_u, dv_H_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, fresh_z_ne_v, dv_H_z, (Ne.symm dv_x_z), fresh_z_ne_u, (Ne.symm dv_y_z), dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_w, fresh_w_ne_v, dv_H_w, dv_w_x, fresh_w_ne_u, dv_w_y, dv_R_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show z ≠ w from (by exact Ne.symm dv_w_z))
  have dv_cache_0012 : y ∉ ((syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, dv_H_y, fresh_y_ne_v, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classEq (.cv x) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_wa (syn_wf1 H A B) (.classMem (.cv v) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, dv_H_x, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, fresh_x_ne_u, dv_H_x, dv_x_y, fresh_x_ne_v, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_wa (syn_wf1 H A B) (.classMem (.cv u) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, dv_H_y, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((syn_wbr (.cv v) R (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, fresh_y_ne_u, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : v ∉ ((syn_wa (syn_wf1 H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, fresh_v_not_B, fresh_v_not_H, fresh_v_not_S, fresh_v_ne_z, fresh_v_ne_x, fresh_v_ne_w, fresh_v_ne_y, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : u ∉ ((syn_wa (syn_wf1 H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, fresh_u_not_B, fresh_u_not_H, fresh_u_not_S, fresh_u_ne_z, fresh_u_ne_x, fresh_u_ne_w, fresh_u_ne_y, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : v ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0026 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : v ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : v ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : u ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : v ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : v ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : u ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wf1o H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))
  have p0001 :=
    @g_f1of1 A B H
  have p0002 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u)))))
  have p0003 :=
    @g_eleq2 S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))) (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u)))
  have p0004 :=
    @g_fvex (.cv v) H
  have p0005 :=
    @g_fvex (.cv u) H
  have p0006 :=
    @g_eqeq1 (.cv z) (syn_cfv H (.cv v)) (syn_cfv H (.cv x))
  have p0007 :=
    @g_anbi1d (.classEq (.cv z) (syn_cfv H (.cv v))) (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y))) p0006
  have p0008 :=
    @g_anbi1d (.classEq (.cv z) (syn_cfv H (.cv v))) (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)) p0007
  have p0009 :=
    @g_n_2rexbidv (.classEq (.cv z) (syn_cfv H (.cv v))) (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))) x y A A dv_cache_0001 dv_cache_0002 p0008
  have p0010 :=
    @g_eqeq1 (.cv w) (syn_cfv H (.cv u)) (syn_cfv H (.cv y))
  have p0011 :=
    @g_anbi2d (.classEq (.cv w) (syn_cfv H (.cv u))) (.classEq (.cv w) (syn_cfv H (.cv y))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) p0010
  have p0012 :=
    @g_anbi1d (.classEq (.cv w) (syn_cfv H (.cv u))) (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)) p0011
  have p0013 :=
    @g_n_2rexbidv (.classEq (.cv w) (syn_cfv H (.cv u))) (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))) x y A A dv_cache_0003 dv_cache_0004 p0012
  have p0014 :=
    @g_opelopab (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))) (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))) (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))) z w (syn_cfv H (.cv v)) (syn_cfv H (.cv u)) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0004 p0005 p0009 p0013
  have p0015 :=
    @g_anass (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0016 :=
    @g_f1fveq A B (.cv v) (.cv x) H
  have p0017 :=
    @g_eqcom (.cv v) (.cv x)
  have p0018 :=
    @g_syl6bb (syn_wa (syn_wf1 H A B) (syn_wa (.classMem (.cv v) A) (.classMem (.cv x) A))) (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv v) (.cv x)) (.classEq (.cv x) (.cv v)) p0016 p0017
  have p0019 :=
    @g_anassrs (syn_wf1 H A B) (.classMem (.cv v) A) (.classMem (.cv x) A) (syn_wb (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv x) (.cv v))) p0018
  have p0020 :=
    @g_anbi1d (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A)) (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (.cv x) (.cv v)) (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))) p0019
  have p0021 :=
    @g_syl5bb (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)))) (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A)) (syn_wa (.classEq (.cv x) (.cv v)) (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)))) p0015 p0020
  have p0022 :=
    @g_rexbidv (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A)) (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (.classEq (.cv x) (.cv v)) (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)))) y A dv_cache_0012 p0021
  have p0023 :=
    @g_r19_42v (.classEq (.cv x) (.cv v)) (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))) y A dv_cache_0013
  have p0024 :=
    @g_syl6bb (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (.classMem (.cv x) A)) (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))) (syn_wrex y A (syn_wa (.classEq (.cv x) (.cv v)) (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))))) (syn_wa (.classEq (.cv x) (.cv v)) (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))))) p0022 p0023
  have p0025 :=
    @g_rexbidva (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))) (syn_wa (.classEq (.cv x) (.cv v)) (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))))) x A dv_cache_0014 p0024
  have p0026 :=
    @g_breq1 (.cv x) (.cv v) (.cv y) R
  have p0027 :=
    @g_anbi2d (.classEq (.cv x) (.cv v)) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv v) R (.cv y)) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) p0026
  have p0028 :=
    @g_rexbidv (.classEq (.cv x) (.cv v)) (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y))) y A dv_cache_0013 p0027
  have p0029 :=
    @g_ceqsrexv (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)))) (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y)))) x (.cv v) A dv_cache_0015 dv_cache_0016 dv_cache_0017 p0028
  have p0030 :=
    @g_adantl (.classMem (.cv v) A) (syn_wb (syn_wrex x A (syn_wa (.classEq (.cv x) (.cv v)) (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)))))) (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y))))) (syn_wf1 H A B) p0029
  have p0031 :=
    @g_bitrd (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))) (syn_wrex x A (syn_wa (.classEq (.cv x) (.cv v)) (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)))))) (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y)))) p0025 p0030
  have p0032 :=
    @g_f1fveq A B (.cv u) (.cv y) H
  have p0033 :=
    @g_eqcom (.cv u) (.cv y)
  have p0034 :=
    @g_syl6bb (syn_wa (syn_wf1 H A B) (syn_wa (.classMem (.cv u) A) (.classMem (.cv y) A))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (.classEq (.cv u) (.cv y)) (.classEq (.cv y) (.cv u)) p0032 p0033
  have p0035 :=
    @g_anassrs (syn_wf1 H A B) (.classMem (.cv u) A) (.classMem (.cv y) A) (syn_wb (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (.classEq (.cv y) (.cv u))) p0034
  have p0036 :=
    @g_anbi1d (syn_wa (syn_wa (syn_wf1 H A B) (.classMem (.cv u) A)) (.classMem (.cv y) A)) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (.classEq (.cv y) (.cv u)) (syn_wbr (.cv v) R (.cv y)) p0035
  have p0037 :=
    @g_rexbidva (syn_wa (syn_wf1 H A B) (.classMem (.cv u) A)) (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y))) (syn_wa (.classEq (.cv y) (.cv u)) (syn_wbr (.cv v) R (.cv y))) y A dv_cache_0018 p0036
  have p0038 :=
    @g_breq2 (.cv y) (.cv u) (.cv v) R
  have p0039 :=
    @g_ceqsrexv (syn_wbr (.cv v) R (.cv y)) (syn_wbr (.cv v) R (.cv u)) y (.cv u) A dv_cache_0019 dv_cache_0020 dv_cache_0021 p0038
  have p0040 :=
    @g_adantl (.classMem (.cv u) A) (syn_wb (syn_wrex y A (syn_wa (.classEq (.cv y) (.cv u)) (syn_wbr (.cv v) R (.cv y)))) (syn_wbr (.cv v) R (.cv u))) (syn_wf1 H A B) p0039
  have p0041 :=
    @g_bitrd (syn_wa (syn_wf1 H A B) (.classMem (.cv u) A)) (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y)))) (syn_wrex y A (syn_wa (.classEq (.cv y) (.cv u)) (syn_wbr (.cv v) R (.cv y)))) (syn_wbr (.cv v) R (.cv u)) p0037 p0040
  have p0042 :=
    @g_sylan9bb (syn_wa (syn_wf1 H A B) (.classMem (.cv v) A)) (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))) (syn_wrex y A (syn_wa (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y))) (syn_wbr (.cv v) R (.cv y)))) (syn_wa (syn_wf1 H A B) (.classMem (.cv u) A)) (syn_wbr (.cv v) R (.cv u)) p0031 p0041
  have p0043 :=
    @g_anandis (syn_wf1 H A B) (.classMem (.cv v) A) (.classMem (.cv u) A) (syn_wb (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))) (syn_wbr (.cv v) R (.cv u))) p0042
  have p0044 :=
    @g_syl5bb (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))) (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (syn_cfv H (.cv v)) (syn_cfv H (.cv x))) (.classEq (syn_cfv H (.cv u)) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))) (syn_wa (syn_wf1 H A B) (syn_wa (.classMem (.cv v) A) (.classMem (.cv u) A))) (syn_wbr (.cv v) R (.cv u)) p0014 p0043
  have p0045 :=
    @g_sylan9bbr (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))) (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) S) (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))) (syn_wa (syn_wf1 H A B) (syn_wa (.classMem (.cv v) A) (.classMem (.cv u) A))) (syn_wbr (.cv v) R (.cv u)) p0003 p0044
  have p0046 :=
    @g_an32s (syn_wf1 H A B) (syn_wa (.classMem (.cv v) A) (.classMem (.cv u) A)) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))) (syn_wb (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) S) (syn_wbr (.cv v) R (.cv u))) p0045
  have p0047 :=
    @g_syl5rbb (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u))) (.classMem (syn_cop (syn_cfv H (.cv v)) (syn_cfv H (.cv u))) S) (syn_wa (syn_wa (syn_wf1 H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))) (syn_wa (.classMem (.cv v) A) (.classMem (.cv u) A))) (syn_wbr (.cv v) R (.cv u)) p0002 p0046
  have p0048 :=
    @g_ralrimivva (syn_wa (syn_wf1 H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))) (syn_wb (syn_wbr (.cv v) R (.cv u)) (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u)))) v u A A dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 p0047
  have p0049 :=
    @g_sylan (syn_wf1o H A B) (syn_wf1 H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y))))))) (syn_wral v A (syn_wral u A (syn_wb (syn_wbr (.cv v) R (.cv u)) (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u)))))) p0001 p0048
  have p0050 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso v u A B R S H dv_cache_0026 dv_cache_0022 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0025
  have p0051 :=
    @g_sylanbrc (syn_wa (syn_wf1o H A B) (.classEq S (syn_copab z w (syn_wrex x A (syn_wrex y A (syn_wa (syn_wa (.classEq (.cv z) (syn_cfv H (.cv x))) (.classEq (.cv w) (syn_cfv H (.cv y)))) (syn_wbr (.cv x) R (.cv y)))))))) (syn_wf1o H A B) (syn_wral v A (syn_wral u A (syn_wb (syn_wbr (.cv v) R (.cv u)) (syn_wbr (syn_cfv H (.cv v)) S (syn_cfv H (.cv u)))))) (syn_wiso H R S A B) p0000 p0049 p0050
  exact p0051

#print axioms g_f1oiso

end NFChoice.DirectNominalPrf.WPPReplay
