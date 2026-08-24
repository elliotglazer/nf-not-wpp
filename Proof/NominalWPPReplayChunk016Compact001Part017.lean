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
import NominalWPPReplayChunk016Compact001Part016

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

noncomputable def g_wecutisouniondmcutorwholendv
    (y : Var) (D : Class) (R : Class) (S : Class) (E : Class) (dv_D_y : y ∉ D.fv) (dv_E_y : y ∉ E.fv) (dv_R_y : y ∉ R.fv) (dv_S_y : y ∉ S.fv) (hyp_wecutisouniondmcutorwholendv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisouniondmcutorwholendv_2 : Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf (syn_wo (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cdm (syn_cuni (syn_cwecutiso R D S E)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cdm (syn_cuni (syn_cwecutiso R D S E)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, dv_E_y, dv_R_y, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : y ∉ ((Wff.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, dv_E_y, dv_R_y, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_orc (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0001 :=
    @g_wecutisouniondmrnss D R S E
  have p0002 :=
    @g_simpl (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_a1i (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) p0003
  have p0005 :=
    @g_id (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))
  have p0006 :=
    @g_jca (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) p0004 p0005
  have p0007 :=
    @g_dfpss2 (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D
  have p0008 :=
    @g_sylibr (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (syn_wa (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D))) (syn_wpss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) p0006 p0007
  have p0009 :=
    @g_dfpss3 (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D
  have p0010 :=
    @g_sylib (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (syn_wpss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wa (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))) p0008 p0009
  have p0011 :=
    @g_simpr (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
  have p0012 :=
    @g_syl (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (syn_wa (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))) (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0010 p0011
  have p0013 :=
    @g_nss x D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) dv_cache_0001 dv_cache_0002
  have p0014 :=
    @g_sylib (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (.neg (syn_wss D (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wex x (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))) p0012 p0013
  have p0015 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x D (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))))
  have p0016 :=
    @g_sylibr (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (syn_wex x (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))))) (syn_wrex x D (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))) p0014 p0015
  have p0017 :=
    @g_dmex (syn_cuni (syn_cwecutiso R D S E)) hyp_wecutisouniondmcutorwholendv_2
  have p0018 :=
    @g_wedifleastssndv x y (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D R dv_cache_0002 dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_wecutisouniondmcutorwholendv_1 p0017
  have p0019 :=
    @g_syl (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (syn_wrex x D (.neg (.classMem (.cv x) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima R (syn_csn (.cv y)))))) p0016 p0018
  have p0020 :=
    @g_wecutisouniondmexactcutndv y D R S E hyp_wecutisouniondmcutorwholendv_1
  have p0021 :=
    @g_exp31 (.classMem (.cv y) D) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima R (syn_csn (.cv y)))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0020
  have p0022 :=
    @g_imp3a (.classMem (.cv y) D) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima R (syn_csn (.cv y)))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0021
  have p0023 :=
    @g_a1i (.imp (.classMem (.cv y) D) (.imp (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima R (syn_csn (.cv y))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) p0022
  have p0024 :=
    @g_imp (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (.classMem (.cv y) D) (.imp (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima R (syn_csn (.cv y))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0023
  have p0025 :=
    @g_reximdva (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima R (syn_csn (.cv y))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) y D dv_cache_0008 p0024
  have p0026 :=
    @g_mpd (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif D (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima R (syn_csn (.cv y)))))) (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0019 p0025
  have p0027 :=
    @g_olcd (.neg (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)) (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) p0026
  have p0028 :=
    @g_pm2_61i (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wo (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) p0000 p0027
  exact p0028

noncomputable def g_wecutisounionrncutorwholendv
    (u : Var) (D : Class) (R : Class) (S : Class) (E : Class) (dv_D_u : u ∉ D.fv) (dv_E_u : u ∉ E.fv) (dv_R_u : u ∉ R.fv) (dv_S_u : u ∉ S.fv) (hyp_wecutisounionrncutorwholendv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) (hyp_wecutisounionrncutorwholendv_2 : Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (E).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_crn (syn_cuni (syn_cwecutiso R D S E)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_crn (syn_cuni (syn_cwecutiso R D S E)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_u, dv_E_u, dv_R_u, dv_S_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have dv_cache_0008 : u ∉ ((Wff.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_u, dv_E_u, dv_R_u, dv_S_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_orc (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
  have p0001 :=
    @g_wecutisouniondmrnss D R S E
  have p0002 :=
    @g_simpr (syn_wss (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_a1i (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) p0003
  have p0005 :=
    @g_id (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
  have p0006 :=
    @g_jca (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) p0004 p0005
  have p0007 :=
    @g_dfpss2 (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E
  have p0008 :=
    @g_sylibr (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wa (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))) (syn_wpss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) p0006 p0007
  have p0009 :=
    @g_dfpss3 (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E
  have p0010 :=
    @g_sylib (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wpss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wa (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) p0008 p0009
  have p0011 :=
    @g_simpr (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0012 :=
    @g_syl (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wa (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0010 p0011
  have p0013 :=
    @g_nss x E (syn_crn (syn_cuni (syn_cwecutiso R D S E))) dv_cache_0001 dv_cache_0002
  have p0014 :=
    @g_sylib (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (.neg (syn_wss E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (syn_wex x (syn_wa (.classMem (.cv x) E) (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))) p0012 p0013
  have p0015 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x E (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))))
  have p0016 :=
    @g_sylibr (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wex x (syn_wa (.classMem (.cv x) E) (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))))) (syn_wrex x E (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) p0014 p0015
  have p0017 :=
    @g_rnex (syn_cuni (syn_cwecutiso R D S E)) hyp_wecutisounionrncutorwholendv_2
  have p0018 :=
    @g_wedifleastssndv x u (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E S dv_cache_0002 dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_wecutisounionrncutorwholendv_1 p0017
  have p0019 :=
    @g_syl (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wrex x E (.neg (.classMem (.cv x) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wrex u E (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u)))))) p0016 p0018
  have p0020 :=
    @g_wecutisounionrnexactcutndv u D R S E hyp_wecutisounionrncutorwholendv_1
  have p0021 :=
    @g_exp31 (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u)))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0020
  have p0022 :=
    @g_imp3a (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u)))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0021
  have p0023 :=
    @g_a1i (.imp (.classMem (.cv u) E) (.imp (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) p0022
  have p0024 :=
    @g_imp (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (.classMem (.cv u) E) (.imp (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0023
  have p0025 :=
    @g_reximdva (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) u E dv_cache_0008 p0024
  have p0026 :=
    @g_mpd (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wrex u E (syn_wa (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u)))))) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0019 p0025
  have p0027 :=
    @g_olcd (.neg (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) p0026
  have p0028 :=
    @g_pm2_61i (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))) p0000 p0027
  exact p0028

noncomputable def g_wecutisogencodeparts
    (x : Var) (D : Class) (R : Class) (hyp_wecutisogencodeparts_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv x) D) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((syn_chnwcutcode R D (.cv x))).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, fresh_u_not_D, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Wff.imp (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, fresh_u_not_D, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutcodecnndv x D R hyp_wecutisogencodeparts_1
  have p0001 :=
    @g_hnwcutcodecnndv x D R hyp_wecutisogencodeparts_1
  have p0002 :=
    @g_elex (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)
  have p0003 :=
    @g_syl (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_id (.classEq (.cv u) (syn_chnwcutcode R D (.cv x)))
  have p0005 :=
    @g_eleq1d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (.cv u) (syn_chnwcutcode R D (.cv x)) (syn_chwcn D) p0004
  have p0006 :=
    @g_id (.classEq (.cv u) (syn_chnwcutcode R D (.cv x)))
  have p0007 :=
    @g_id (.classEq (.cv u) (syn_chnwcutcode R D (.cv x)))
  have p0008 :=
    @g_fveq2d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (.cv u) (syn_chnwcutcode R D (.cv x)) (syn_c1st) p0007
  have p0009 :=
    @g_id (.classEq (.cv u) (syn_chnwcutcode R D (.cv x)))
  have p0010 :=
    @g_fveq2d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (.cv u) (syn_chnwcutcode R D (.cv x)) (syn_c2nd) p0009
  have p0011 :=
    @g_opeq12d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) p0008 p0010
  have p0012 :=
    @g_eqeq12d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (.cv u) (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))) p0006 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv u) (syn_chnwcutcode R D (.cv x))) (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))))) p0005 p0012
  have p0014 :=
    @g_hwcnpair u D
  have p0015 :=
    @g_vtoclg (.imp (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.imp (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))))) u (syn_chnwcutcode R D (.cv x)) (syn_cvv) dv_cache_0001 dv_cache_0002 p0013 p0014
  have p0016 :=
    @g_syl (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_cvv)) (.imp (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))))) p0003 p0015
  have p0017 :=
    @g_mpd (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))))) p0000 p0016
  have p0018 :=
    @g_eqcomd (.classMem (.cv x) D) (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))) p0017
  have p0019 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x))))
  have p0020 :=
    @g_a1i (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv x) D) p0019
  have p0021 :=
    @g_eqtrd (.classMem (.cv x) D) (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))) (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0018 p0020
  have p0022 :=
    @g_opth (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0023 :=
    @g_sylib (.classMem (.cv x) D) (.classEq (syn_cop (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x)))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode R D (.cv x))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode R D (.cv x))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0021 p0022
  exact p0023

#print axioms g_wecutisogencodeparts

end NFChoice.DirectNominalPrf.WPPReplay
