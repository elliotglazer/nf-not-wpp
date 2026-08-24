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
import NominalWPPReplayChunk017Compact001Part079

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

noncomputable def g_hnwcutambfactorranbrimpndv
    (x : Var) (z : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (dv_x_z : x ≠ z) (hyp_hnwcutambfactorranbrimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wb (.classMem (.cv z) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({z} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_ne_z : p ≠ z := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_p : z ≠ p :=
    Ne.symm fresh_p_ne_z
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_p : u ≠ p :=
    Ne.symm fresh_p_ne_u
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_z : q ≠ z := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_q : z ≠ q :=
    Ne.symm fresh_q_ne_z
  have fresh_q_ne_u : q ≠ u := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ u from (by exact fresh_p_ne_u))
  have dv_cache_0007 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint (({x} : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({x} : Finset Var)) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) (({u} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ u from (by exact Ne.symm dv_u_x)))))))), (show Disjoint (({x} : Finset Var)) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint (({x} : Finset Var)) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0008 : x ∉ ((syn_cuni (syn_cuni (.cv p)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, (Ne.symm dv_u_x), dv_A_x, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, fresh_x_ne_p, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_u, fresh_p_ne_x, fresh_p_not_A, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_u, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : q ∉ ((syn_csn (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : q ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0017 : Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint (((syn_cuni (.cv q))).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (((syn_cuni (.cv q))).fv) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv q)).fv) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) (({u} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show q ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ u from (by exact fresh_q_ne_u)))))))))))), (show Disjoint (((syn_cuni (.cv q))).fv) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv q)).fv) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint (({q} : Finset Var)) ((∅ : Finset Var)) from (by simp))))))))⟩))))
  have dv_cache_0018 : p ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((Wff.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, fresh_p_not_A, fresh_p_ne_u, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_u, fresh_q_ne_p, fresh_q_not_A, fresh_q_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_u, fresh_q_not_A, fresh_q_ne_x, fresh_q_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), fresh_x_ne_p, dv_A_x, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutambfactorf1impndv u A dv_cache_0001 hyp_hnwcutambfactorranbrimpndv_1
  have p0001 :=
    @g_f1fn (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0002 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A)) (syn_wfn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0000 p0001
  have p0003 :=
    @g_fvelrnb p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.cv z) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wfn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wb (.classMem (.cv z) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) p0002 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
  have p0006 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0005 p0006
  have p0008 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
  have p0009 :=
    @g_hnwcutambfactorvalimpndv u A p dv_cache_0005 dv_cache_0001 dv_cache_0006 hyp_hnwcutambfactorranbrimpndv_1
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classMem (.cv u) (syn_chwcn A)) (.imp (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)))) p0008 p0009
  have p0011 :=
    @g_mpd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A))) p0007 p0010
  have p0012 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
  have p0013 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))
  have p0014 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)) p0012 p0013
  have p0015 :=
    @g_eqtr3d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (.cv z) p0011 p0014
  have p0016 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
  have p0017 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0016 p0017
  have p0019 :=
    @g_pw12argcl (.cv p) (syn_cfv (syn_c2nd) (.cv u))
  have p0020 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))))) p0018 p0019
  have p0021 :=
    @g_simpld (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))) p0020
  have p0022 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p))))
  have p0023 :=
    @g_hnwcutcodeeq3 (.cv x) (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0007
  have p0024 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p))))) (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p)))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p))))) p0022 p0023
  have p0025 :=
    @g_eceq1 (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p))))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p))))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A))) p0024 p0025
  have p0027 :=
    @g_eqeq1d (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p))))) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (.cv z) p0026
  have p0028 :=
    @g_rspcedv (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (.cv z)) x (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0021 p0027
  have p0029 :=
    @g_mpd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (.cv z)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0015 p0028
  have p0030 :=
    @g_n_3impb (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0029
  have p0031 :=
    @g_n_3exp (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0030
  have p0032 :=
    @g_rexlimdv (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0012 dv_cache_0013 p0031
  have p0033 :=
    @g_imp (.classMem (.cv u) (syn_chwcn A)) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0032
  have p0034 :=
    @g_snex (syn_csn (.cv x))
  have p0035 :=
    @g_isseti q (syn_csn (syn_csn (.cv x))) dv_cache_0014 p0034
  have p0036 :=
    @g_a1i (syn_wex q (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0035
  have p0037 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0038 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))
  have p0039 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0037 p0038
  have p0040 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0041 :=
    @g_snelpw1 (.cv x) (syn_cfv (syn_c2nd) (.cv u))
  have p0042 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0041
  have p0043 :=
    @g_mpbird (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0040 p0042
  have p0044 :=
    @g_snelpw1 (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))
  have p0045 :=
    @g_a1i (syn_wb (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0044
  have p0046 :=
    @g_mpbird (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0043 p0045
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0039 p0046
  have p0048 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0049 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.cv q) (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0048
  have p0050 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0047 p0049
  have p0051 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0052 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0051 p0052
  have p0054 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0055 :=
    @g_snelpw1 (.cv x) (syn_cfv (syn_c2nd) (.cv u))
  have p0056 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0055
  have p0057 :=
    @g_mpbird (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0054 p0056
  have p0058 :=
    @g_snelpw1 (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))
  have p0059 :=
    @g_a1i (syn_wb (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0058
  have p0060 :=
    @g_mpbird (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0057 p0059
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0053 p0060
  have p0062 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0063 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.cv q) (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0062
  have p0064 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0061 p0063
  have p0065 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0066 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))
  have p0067 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0065 p0066
  have p0068 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0069 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) p0067 p0068
  have p0070 :=
    @g_hnwcutambfactorvalimpndv u A q dv_cache_0015 dv_cache_0001 dv_cache_0016 hyp_hnwcutambfactorranbrimpndv_1
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.classMem (.cv u) (syn_chwcn A)) (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))) p0069 p0070
  have p0072 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) p0064 p0071
  have p0073 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0074 :=
    @g_unieqd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.cv q) (syn_csn (syn_csn (.cv x))) p0073
  have p0075 :=
    @g_unieqd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_cuni (.cv q)) (syn_cuni (syn_csn (syn_csn (.cv x)))) p0074
  have p0076 :=
    @g_snex (.cv x)
  have p0077 :=
    @g_unisn (syn_csn (.cv x)) p0076
  have p0078 :=
    @g_unieqi (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x)) p0077
  have p0079 :=
    @g_vex x
  have p0080 :=
    @g_unisn (.cv x) p0079
  have p0081 :=
    @g_eqtri (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x))))) (syn_cuni (syn_csn (.cv x))) (.cv x) p0078 p0080
  have p0082 :=
    @g_a1i (.classEq (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x))))) (.cv x)) (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) p0081
  have p0083 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x))))) (.cv x) p0075 p0082
  have p0084 :=
    @g_hnwcutcodeeq3 (syn_cuni (syn_cuni (.cv q))) (.cv x) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0017
  have p0085 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.classEq (syn_cuni (syn_cuni (.cv q))) (.cv x)) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) p0083 p0084
  have p0086 :=
    @g_eceq1 (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)
  have p0087 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A))) p0085 p0086
  have p0088 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) p0072 p0087
  have p0089 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0090 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)) p0089 p0090
  have p0092 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z) p0088 p0091
  have p0093 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (.cv z)) p0050 p0092
  have p0094 :=
    @g_id (.classEq (.cv p) (.cv q))
  have p0095 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0094
  have p0096 :=
    @g_eqeq1d (.classEq (.cv p) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (.cv z) p0095
  have p0097 :=
    @g_rspcev (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (.cv z)) p (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0018 dv_cache_0002 dv_cache_0019 p0096
  have p0098 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)) (.cv z))) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) p0093 p0097
  have p0099 :=
    @g_exlimddv (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) q dv_cache_0020 dv_cache_0021 p0036 p0098
  have p0100 :=
    @g_ex (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) p0099
  have p0101 :=
    @g_ex (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.imp (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))) p0100
  have p0102 :=
    @g_rexlimdv (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0022 dv_cache_0023 p0101
  have p0103 :=
    @g_imp (.classMem (.cv u) (syn_chwcn A)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) p0102
  have p0104 :=
    @g_impbida (.classMem (.cv u) (syn_chwcn A)) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0033 p0103
  have p0105 :=
    @g_bitrd (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0004 p0104
  exact p0105

#print axioms g_hnwcutambfactorranbrimpndv

end NFChoice.DirectNominalPrf.WPPReplay
