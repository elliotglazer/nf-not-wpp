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
import NominalWPPReplayChunk017Compact001Part088

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

noncomputable def g_cfbhnqinjcodecoverdclndv
    (C : Class) (P : Class) (k : Var) (Y : Class) (dv_P_k : k ∉ P.fv) (dv_Y_k : k ∉ Y.fv) (hyp_cfbhnqinjcodecoverdclndv_1 : Nominal.NPrf (.classMem P (syn_cvv))) (hyp_cfbhnqinjcodecoverdclndv_2 : Nominal.NPrf (.classMem Y (syn_cvv))) (hyp_cfbhnqinjcodecoverdclndv_3 : Nominal.NPrf (.classMem C (syn_chwcn P))) :
    Nominal.NPrf (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y) (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P))) (syn_crn (syn_chnqinc Y (syn_cun P Y))))) := by
  let proofSupport : Finset Var := C.fv ∪ P.fv ∪ ({k} : Finset Var) ∪ Y.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_P : u ∉ P.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_k : u ≠ k := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_u : k ≠ u :=
    Ne.symm fresh_u_ne_k
  have fresh_u_not_Y : u ∉ Y.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (P).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_P_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (P).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ (Y).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_Y_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ (Y).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_Y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : k ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show k ≠ u from (by exact fresh_k_ne_u))
  have dv_cache_0006 : u ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((Wff.imp (.classMem C (syn_chwcn P)) (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y) (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P))) (syn_crn (syn_chnqinc Y (syn_cun P Y))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, fresh_u_not_P, fresh_u_not_Y, fresh_u_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex C (syn_chwcn P)
  have p0001 :=
    Nominal.mp hyp_cfbhnqinjcodecoverdclndv_3 p0000
  have p0002 :=
    @g_id (.classEq (.cv u) C)
  have p0003 :=
    @g_eleq1d (.classEq (.cv u) C) (.cv u) C (syn_chwcn P) p0002
  have p0004 :=
    @g_id (.classEq (.cv u) C)
  have p0005 :=
    @g_fveq2d (.classEq (.cv u) C) (.cv u) C (syn_c2nd) p0004
  have p0006 :=
    @g_f1eq2 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) C) Y (.cv k)
  have p0007 :=
    @g_syl (.classEq (.cv u) C) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) C)) (syn_wb (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y)) p0005 p0006
  have p0008 :=
    @g_id (.classEq (.cv u) C)
  have p0009 :=
    @g_eceq1 (.cv u) C (syn_chwniso P)
  have p0010 :=
    @g_syl (.classEq (.cv u) C) (.classEq (.cv u) C) (.classEq (syn_cec (.cv u) (syn_chwniso P)) (syn_cec C (syn_chwniso P))) p0008 p0009
  have p0011 :=
    @g_fveq2d (.classEq (.cv u) C) (syn_cec (.cv u) (syn_chwniso P)) (syn_cec C (syn_chwniso P)) (syn_chnqinc P (syn_cun P Y)) p0010
  have p0012 :=
    @g_eleq1d (.classEq (.cv u) C) (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P))) (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P))) (syn_crn (syn_chnqinc Y (syn_cun P Y))) p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv u) C) (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y) (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P))) (syn_crn (syn_chnqinc Y (syn_cun P Y)))) (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P))) (syn_crn (syn_chnqinc Y (syn_cun P Y)))) p0007 p0012
  have p0014 :=
    @g_imbi12d (.classEq (.cv u) C) (.classMem (.cv u) (syn_chwcn P)) (.classMem C (syn_chwcn P)) (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P))) (syn_crn (syn_chnqinc Y (syn_cun P Y))))) (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y) (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P))) (syn_crn (syn_chnqinc Y (syn_cun P Y))))) p0003 p0013
  have p0015 :=
    @g_cfbhnqinjcodecoverddndv u P k Y dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 hyp_cfbhnqinjcodecoverdclndv_1 hyp_cfbhnqinjcodecoverdclndv_2
  have p0016 :=
    @g_vtoclg (.imp (.classMem (.cv u) (syn_chwcn P)) (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P))) (syn_crn (syn_chnqinc Y (syn_cun P Y)))))) (.imp (.classMem C (syn_chwcn P)) (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) C) Y) (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec C (syn_chwniso P))) (syn_crn (syn_chnqinc Y (syn_cun P Y)))))) u C (syn_cvv) dv_cache_0006 dv_cache_0007 p0014 p0015
  have p0017 :=
    Nominal.mp p0001 p0016
  have p0018 :=
    Nominal.mp hyp_cfbhnqinjcodecoverdclndv_3 p0017
  exact p0018

#print axioms g_cfbhnqinjcodecoverdclndv

end NFChoice.DirectNominalPrf.WPPReplay
