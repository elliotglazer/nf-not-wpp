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
import NominalWPPReplayChunk013Compact001Part015

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

noncomputable def g_clos1induct
    (x : Var) (z : Var) (C : Class) (R : Class) (S : Class) (V : Class) (X : Class) (dv_C_x : x ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_R_x : x ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_X_x : x ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_x_z : x ≠ z) (hyp_clos1induct_1 : Nominal.NPrf (.classMem S (syn_cvv))) (hyp_clos1induct_2 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_clos1induct_3 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) :
    Nominal.NPrf (.imp (syn_w3a (.classMem X V) (syn_wss S X) (syn_wral x C (.all z (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X))))) (syn_wss C X)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({z} : Finset Var) ∪ C.fv ∪ R.fv ∪ S.fv ∪ V.fv ∪ X.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_V : a ∉ V.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cin X C)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_x, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_z, dv_X_x, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cima R (syn_cin X C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, dv_X_z, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cin X C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_z, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0009 : a ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_cin X C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_X, fresh_a_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((syn_wa (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, fresh_a_not_X, fresh_a_not_C, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_clos1ex R S hyp_clos1induct_1 hyp_clos1induct_2
  have p0001 :=
    @g_eqeltri C (syn_cclos1 S R) (syn_cvv) hyp_clos1induct_3 p0000
  have p0002 :=
    @g_inexg X C V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem X V) (.classMem C (syn_cvv)) (.classMem (syn_cin X C) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_clos1base C R S hyp_clos1induct_3
  have p0005 :=
    @g_ssin S X C
  have p0006 :=
    @g_biimpi (syn_wa (syn_wss S X) (syn_wss S C)) (syn_wss S (syn_cin X C)) p0005
  have p0007 :=
    @g_mpan2 (syn_wss S X) (syn_wss S C) (syn_wss S (syn_cin X C)) p0004 p0006
  have p0008 :=
    @g_elima2 x (.cv z) R (syn_cin X C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_elin (.cv z) X C
  have p0010 :=
    @g_imbi12i (.classMem (.cv z) (syn_cima R (syn_cin X C))) (syn_wex x (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z)))) (.classMem (.cv z) (syn_cin X C)) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)) p0008 p0009
  have p0011 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))))
  have p0012 :=
    @g_impexp (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)
  have p0013 :=
    @g_clos1conn (.cv x) (.cv z) C R S hyp_clos1induct_3
  have p0014 :=
    @g_biantrud (syn_wa (.classMem (.cv x) C) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) C) (.classMem (.cv z) X) p0013
  have p0015 :=
    @g_adantrl (.classMem (.cv x) C) (syn_wbr (.cv x) R (.cv z)) (syn_wb (.classMem (.cv z) X) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))) (.classMem (.cv x) X) p0014
  have p0016 :=
    @g_pm5_74i (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) (.classMem (.cv z) X) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)) p0015
  have p0017 :=
    @g_bitr3i (.imp (.classMem (.cv x) C) (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X))) (.imp (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) (.classMem (.cv z) X)) (.imp (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))) p0012 p0016
  have p0018 :=
    @g_albii (.imp (.classMem (.cv x) C) (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X))) (.imp (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))) x p0017
  have p0019 :=
    @g_bitri (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X))) (.all x (.imp (.classMem (.cv x) C) (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))) (.all x (.imp (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))) p0011 p0018
  have p0020 :=
    @g_elin (.cv x) X C
  have p0021 :=
    @g_ancom (.classMem (.cv x) X) (.classMem (.cv x) C)
  have p0022 :=
    @g_bitri (.classMem (.cv x) (syn_cin X C)) (syn_wa (.classMem (.cv x) X) (.classMem (.cv x) C)) (syn_wa (.classMem (.cv x) C) (.classMem (.cv x) X)) p0020 p0021
  have p0023 :=
    @g_anbi1i (.classMem (.cv x) (syn_cin X C)) (syn_wa (.classMem (.cv x) C) (.classMem (.cv x) X)) (syn_wbr (.cv x) R (.cv z)) p0022
  have p0024 :=
    @g_anass (.classMem (.cv x) C) (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))
  have p0025 :=
    @g_bitri (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z))) (syn_wa (syn_wa (.classMem (.cv x) C) (.classMem (.cv x) X)) (syn_wbr (.cv x) R (.cv z))) (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) p0023 p0024
  have p0026 :=
    @g_imbi1i (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z))) (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)) p0025
  have p0027 :=
    @g_albii (.imp (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))) (.imp (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))) x p0026
  have p0028 :=
    @g_n_19_23v (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)) x dv_cache_0004
  have p0029 :=
    @g_n_3bitr2i (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X))) (.all x (.imp (syn_wa (.classMem (.cv x) C) (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z)))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))) (.all x (.imp (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C)))) (.imp (syn_wex x (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z)))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))) p0019 p0027 p0028
  have p0030 :=
    @g_bitr4i (.imp (.classMem (.cv z) (syn_cima R (syn_cin X C))) (.classMem (.cv z) (syn_cin X C))) (.imp (syn_wex x (syn_wa (.classMem (.cv x) (syn_cin X C)) (syn_wbr (.cv x) R (.cv z)))) (syn_wa (.classMem (.cv z) X) (.classMem (.cv z) C))) (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X))) p0010 p0029
  have p0031 :=
    @g_albii (.imp (.classMem (.cv z) (syn_cima R (syn_cin X C))) (.classMem (.cv z) (syn_cin X C))) (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X))) z p0030
  have p0032 :=
    @g_dfss2 z (syn_cima R (syn_cin X C)) (syn_cin X C) dv_cache_0005 dv_cache_0006
  have p0033 :=
    @g_ralcom4 (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)) x z C dv_cache_0007 dv_cache_0008
  have p0034 :=
    @g_n_3bitr4i (.all z (.imp (.classMem (.cv z) (syn_cima R (syn_cin X C))) (.classMem (.cv z) (syn_cin X C)))) (.all z (syn_wral x C (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)) (syn_wral x C (.all z (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))) p0031 p0032 p0033
  have p0035 :=
    @g_biimpri (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)) (syn_wral x C (.all z (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))) p0034
  have p0036 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a dv_cache_0009 dv_cache_0010
  have p0037 :=
    @g_eqtri C (syn_cclos1 S R) (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) hyp_clos1induct_3 p0036
  have p0038 :=
    @g_sseq2 (.cv a) (syn_cin X C) S
  have p0039 :=
    @g_imaeq2 (.cv a) (syn_cin X C) R
  have p0040 :=
    @g_id (.classEq (.cv a) (syn_cin X C))
  have p0041 :=
    @g_sseq12d (.classEq (.cv a) (syn_cin X C)) (syn_cima R (.cv a)) (syn_cima R (syn_cin X C)) (.cv a) (syn_cin X C) p0039 p0040
  have p0042 :=
    @g_anbi12d (.classEq (.cv a) (syn_cin X C)) (syn_wss S (.cv a)) (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (.cv a)) (.cv a)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)) p0038 p0041
  have p0043 :=
    @g_elabg (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (syn_wa (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C))) a (syn_cin X C) (syn_cvv) dv_cache_0011 dv_cache_0012 p0042
  have p0044 :=
    @g_biimprd (.classMem (syn_cin X C) (syn_cvv)) (.classMem (syn_cin X C) (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_wa (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C))) p0043
  have p0045 :=
    @g_n_3impib (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)) (.classMem (syn_cin X C) (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) p0044
  have p0046 :=
    @g_intss1 (syn_cin X C) (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
  have p0047 :=
    @g_syl (syn_w3a (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C))) (.classMem (syn_cin X C) (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_wss (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_cin X C)) p0045 p0046
  have p0048 :=
    @g_syl5eqss (syn_w3a (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C))) C (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))) (syn_cin X C) p0037 p0047
  have p0049 :=
    @g_inss1 X C
  have p0050 :=
    @g_syl6ss (syn_w3a (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S (syn_cin X C)) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C))) C (syn_cin X C) X p0048 p0049
  have p0051 :=
    @g_syl3an (.classMem X V) (.classMem (syn_cin X C) (syn_cvv)) (syn_wss S X) (syn_wss S (syn_cin X C)) (syn_wral x C (.all z (.imp (syn_wa (.classMem (.cv x) X) (syn_wbr (.cv x) R (.cv z))) (.classMem (.cv z) X)))) (syn_wss (syn_cima R (syn_cin X C)) (syn_cin X C)) (syn_wss C X) p0003 p0007 p0035 p0050
  exact p0051

noncomputable def g_clos1is
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (C : Class) (R : Class) (S : Class) (dv_A_x : x ∉ A.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_S_x : x ∉ S.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_clos1is_1 : Nominal.NPrf (.classMem S (syn_cvv))) (hyp_clos1is_2 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_clos1is_3 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) (hyp_clos1is_4 : Nominal.NPrf (.classMem (.cab x ph) (syn_cvv))) (hyp_clos1is_5 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) (hyp_clos1is_6 : Nominal.NPrf (.imp (.objEq x z) (syn_wb ph ch))) (hyp_clos1is_7 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph th))) (hyp_clos1is_8 : Nominal.NPrf (.imp (.classMem (.cv x) S) ph)) (hyp_clos1is_9 : Nominal.NPrf (.imp (syn_w3a (.classMem (.cv y) C) (syn_wbr (.cv y) R (.cv z)) ps) ch)) :
    Nominal.NPrf (.imp (.classMem A C) th) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ C.fv ∪ R.fv ∪ S.fv
  have dv_cache_0001 : x ∉ (S).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ch).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ch_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Wff.classMem (.cv y) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_y_z), dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cab x ph)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Class.cab x ph)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0014 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ (th).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_th_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ssab ph x S dv_cache_0001
  have p0001 :=
    @g_mpgbir (syn_wss S (.cab x ph)) (.imp (.classMem (.cv x) S) ph) x p0000 hyp_clos1is_8
  have p0002 :=
    @g_n_3expib (.classMem (.cv y) C) (syn_wbr (.cv y) R (.cv z)) ps ch hyp_clos1is_9
  have p0003 :=
    @g_vex y
  have p0004_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      hyp_clos1is_5
  have p0004 :=
    @g_elab ph ps x (.cv y) dv_cache_0002 dv_cache_0003 p0003 p0004_e01_recanon
  have p0005 :=
    @g_anbi1i (.classMem (.cv y) (.cab x ph)) ps (syn_wbr (.cv y) R (.cv z)) p0004
  have p0006 :=
    @g_ancom ps (syn_wbr (.cv y) R (.cv z))
  have p0007 :=
    @g_bitri (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z))) (syn_wa ps (syn_wbr (.cv y) R (.cv z))) (syn_wa (syn_wbr (.cv y) R (.cv z)) ps) p0005 p0006
  have p0008 :=
    @g_vex z
  have p0009_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb ph ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      hyp_clos1is_6
  have p0009 :=
    @g_elab ph ch x (.cv z) dv_cache_0004 dv_cache_0005 p0008 p0009_e01_recanon
  have p0010 :=
    @g_n_3imtr4g (.classMem (.cv y) C) (syn_wa (syn_wbr (.cv y) R (.cv z)) ps) ch (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z))) (.classMem (.cv z) (.cab x ph)) p0002 p0007 p0009
  have p0011 :=
    @g_alrimiv (.classMem (.cv y) C) (.imp (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z))) (.classMem (.cv z) (.cab x ph))) z dv_cache_0006 p0010
  have p0012 :=
    @g_rgen (.all z (.imp (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z))) (.classMem (.cv z) (.cab x ph)))) y C p0011
  have p0013 :=
    @g_clos1induct y z C R S (syn_cvv) (.cab x ph) dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 hyp_clos1is_1 hyp_clos1is_2 hyp_clos1is_3
  have p0014 :=
    @g_mp3an (.classMem (.cab x ph) (syn_cvv)) (syn_wss S (.cab x ph)) (syn_wral y C (.all z (.imp (syn_wa (.classMem (.cv y) (.cab x ph)) (syn_wbr (.cv y) R (.cv z))) (.classMem (.cv z) (.cab x ph))))) (syn_wss C (.cab x ph)) hyp_clos1is_4 p0001 p0012 p0013
  have p0015 :=
    @g_sseli C (.cab x ph) A p0014
  have p0016 :=
    @g_elabg ph th x A C dv_cache_0014 dv_cache_0015 hyp_clos1is_7
  have p0017 :=
    @g_mpbid (.classMem A C) (.classMem A (.cab x ph)) th p0015 p0016
  exact p0017

#print axioms g_clos1is

end NFChoice.DirectNominalPrf.WPPReplay
