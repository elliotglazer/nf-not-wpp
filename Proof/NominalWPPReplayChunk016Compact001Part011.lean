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
import NominalWPPReplayChunk016Compact001Part010

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

noncomputable def g_wecutisounionrnexactcutndv
    (u : Var) (D : Class) (R : Class) (S : Class) (E : Class) (hyp_wecutisounionrnexactcutndv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_E, fresh_v_not_S, fresh_v_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((syn_crn (syn_cuni (syn_cwecutiso R D S E)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_D, fresh_v_not_E, fresh_v_not_R, fresh_v_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_E, fresh_v_not_D, fresh_v_not_R, fresh_v_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))
  have p0001 :=
    @g_wecutisounionrnsscutndv u D R S E hyp_wecutisounionrnexactcutndv_1
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0000 p0001
  have p0003 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0004 :=
    @g_elstrictseg u v E S
  have p0005 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wa (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))) p0003 p0004
  have p0006 :=
    @g_simprr (.classMem (.cv v) E) (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u))
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))) (syn_wne (.cv v) (.cv u)) p0005 p0006
  have p0008 :=
    @g_wppweantisym E S
  have p0009 :=
    Nominal.mp hyp_wecutisounionrnexactcutndv_1 p0008
  have p0010 :=
    @g_a1i (syn_wbr S (syn_cantisym) E) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) p0009
  have p0011 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0012 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0013 :=
    @g_elstrictseg u v E S
  have p0014 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wa (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))) p0012 p0013
  have p0015 :=
    @g_simpl (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))) (.classMem (.cv v) E) p0014 p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv v) E) p0011 p0016
  have p0018 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0019 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) p0018 p0019
  have p0021 :=
    @g_simpl (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))
  have p0022 :=
    @g_simpl (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (.classMem (.cv u) E) p0021 p0022
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv u) E) p0020 p0023
  have p0025 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0026 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0027 :=
    @g_elstrictseg u v E S
  have p0028 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wa (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))) p0026 p0027
  have p0029 :=
    @g_simprl (.classMem (.cv v) E) (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u))
  have p0030 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))) (syn_wbr (.cv v) S (.cv u)) p0028 p0029
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wbr (.cv v) S (.cv u)) p0025 p0030
  have p0032 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0033 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) p0032 p0033
  have p0035 :=
    @g_simpr (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u)))) p0034 p0035
  have p0037 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0038 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0039 :=
    @g_elstrictseg u v E S
  have p0040 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wa (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))) p0038 p0039
  have p0041 :=
    @g_simpl (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv v) E) (syn_wa (syn_wbr (.cv v) S (.cv u)) (syn_wne (.cv v) (.cv u)))) (.classMem (.cv v) E) p0040 p0041
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv v) E) p0037 p0042
  have p0044 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
  have p0045 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (.classMem (.cv v) E) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0043 p0044
  have p0046 :=
    @g_eldif (.cv v) E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
  have p0047 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wa (.classMem (.cv v) E) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (.classMem (.cv v) (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) p0045 p0046
  have p0048 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))) (.cv v) p0036 p0047
  have p0049 :=
    @g_elimasn S (.cv u) (.cv v)
  have p0050 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv u) S (.cv v))))
  have p0051 :=
    @g_bitr4i (.classMem (.cv v) (syn_cima S (syn_csn (.cv u)))) (.classMem (syn_cop (.cv u) (.cv v)) S) (syn_wbr (.cv u) S (.cv v)) p0049 p0050
  have p0052 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (.classMem (.cv v) (syn_cima S (syn_csn (.cv u)))) (syn_wbr (.cv u) S (.cv v)) p0048 p0051
  have p0053 :=
    @g_antid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) E S (.cv v) (.cv u) p0010 p0017 p0024 p0031 p0052
  have p0054 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (.classEq (.cv v) (.cv u)) p0053
  have p0055 :=
    @g_necon3ad (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E))))) (.cv v) (.cv u) p0054
  have p0056 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wne (.cv v) (.cv u)) (.neg (.neg (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) p0007 p0055
  have p0057 :=
    @g_notnotrd (syn_wa (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0056
  have p0058 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (.classMem (.cv v) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (.classMem (.cv v) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) p0057
  have p0059 :=
    @g_ssrdv (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) v (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0058
  have p0060 :=
    @g_eqssd (syn_wa (syn_wa (.classMem (.cv u) E) (.neg (.classMem (.cv u) (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))) (syn_wss (syn_cdif E (syn_crn (syn_cuni (syn_cwecutiso R D S E)))) (syn_cima S (syn_csn (.cv u))))) (syn_crn (syn_cuni (syn_cwecutiso R D S E))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) p0002 p0059
  exact p0060

noncomputable def g_wecutisoaddpairf1ondv
    (x : Var) (u : Var) (D : Class) (R : Class) (S : Class) (E : Class) (H : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wf1o (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ H.fv
  have p0000 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0001 :=
    @g_isof1o (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R S H
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wf1o H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0004 :=
    @g_f1osng (.cv x) (.cv u) D E
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wf1o (syn_csn (syn_cop (.cv x) (.cv u))) (syn_csn (.cv x)) (syn_csn (.cv u))) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wf1o H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wf1o (syn_csn (syn_cop (.cv x) (.cv u))) (syn_csn (.cv x)) (syn_csn (.cv u))) p0002 p0005
  have p0007 :=
    @g_strictsegnel x D R
  have p0008 :=
    @g_disjsn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv x)
  have p0009 :=
    @g_mpbir (.classEq (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_c0)) (.neg (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0007 p0008
  have p0010 :=
    @g_a1i (.classEq (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_c0)) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0009
  have p0011 :=
    @g_strictsegnel u E S
  have p0012 :=
    @g_disjsn (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (.cv u)
  have p0013 :=
    @g_mpbir (.classEq (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_c0)) (.neg (.classMem (.cv u) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0011 p0012
  have p0014 :=
    @g_a1i (.classEq (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_c0)) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) p0013
  have p0015 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (.classEq (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_c0)) (.classEq (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_c0)) p0010 p0014
  have p0016 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wf1o H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wf1o (syn_csn (syn_cop (.cv x) (.cv u))) (syn_csn (.cv x)) (syn_csn (.cv u)))) (syn_wa (.classEq (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_c0)) (.classEq (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_c0))) p0006 p0015
  have p0017 :=
    @g_f1oun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv x)) (syn_csn (.cv u)) H (syn_csn (syn_cop (.cv x) (.cv u)))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv u) E)) (syn_wiso H R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (syn_wf1o H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))) (syn_wf1o (syn_csn (syn_cop (.cv x) (.cv u))) (syn_csn (.cv x)) (syn_csn (.cv u)))) (syn_wa (.classEq (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_c0)) (.classEq (syn_cin (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_c0)))) (syn_wf1o (syn_cun H (syn_csn (syn_cop (.cv x) (.cv u)))) (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) p0016 p0017
  exact p0018

#print axioms g_wecutisoaddpairf1ondv

end NFChoice.DirectNominalPrf.WPPReplay
