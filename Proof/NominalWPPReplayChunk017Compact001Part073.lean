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
import NominalWPPReplayChunk017Compact001Part072

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

noncomputable def g_isostrictsegresclndv
    (B : Class) (D : Class) (R : Class) (S : Class) (E : Class) (H : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) := by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ H.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.imp (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, fresh_x_not_E, fresh_x_not_H, fresh_x_not_R, fresh_x_not_S, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wa (syn_wiso H R S D E) (.classMem B D))
  have p0001 :=
    @g_simpr (syn_wiso H R S D E) (.classMem B D)
  have p0002 :=
    @g_elex B D
  have p0003 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem B D)) (.classMem B D) (.classMem B (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_biid (syn_wiso H R S D E)
  have p0005 :=
    @g_a1i (syn_wb (syn_wiso H R S D E) (syn_wiso H R S D E)) (.classEq (.cv x) B) p0004
  have p0006 :=
    @g_id (.classEq (.cv x) B)
  have p0007 :=
    @g_eleq1d (.classEq (.cv x) B) (.cv x) B D p0006
  have p0008 :=
    @g_anbi12d (.classEq (.cv x) B) (syn_wiso H R S D E) (syn_wiso H R S D E) (.classMem (.cv x) D) (.classMem B D) p0005 p0007
  have p0009 :=
    @g_id (.classEq (.cv x) B)
  have p0010 :=
    @g_sneqd (.classEq (.cv x) B) (.cv x) B p0009
  have p0011 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid))) p0010
  have p0012 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0011
  have p0013 :=
    @g_reseq2d (.classEq (.cv x) B) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) H p0012
  have p0014 :=
    @g_isoeq1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0015 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_wb (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) p0013 p0014
  have p0016 :=
    @g_id (.classEq (.cv x) B)
  have p0017 :=
    @g_sneqd (.classEq (.cv x) B) (.cv x) B p0016
  have p0018 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid))) p0017
  have p0019 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0018
  have p0020 :=
    @g_id (.classEq (.cv x) B)
  have p0021 :=
    @g_sneqd (.classEq (.cv x) B) (.cv x) B p0020
  have p0022 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid))) p0021
  have p0023 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0022
  have p0024 :=
    @g_xpeq12d (.classEq (.cv x) B) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) p0019 p0023
  have p0025 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) R p0024
  have p0026 :=
    @g_isoeq2 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
  have p0027 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))) (syn_wb (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) p0025 p0026
  have p0028 :=
    @g_bitrd (.classEq (.cv x) B) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) p0015 p0027
  have p0029 :=
    @g_id (.classEq (.cv x) B)
  have p0030 :=
    @g_fveq2d (.classEq (.cv x) B) (.cv x) B H p0029
  have p0031 :=
    @g_sneqd (.classEq (.cv x) B) (syn_cfv H (.cv x)) (syn_cfv H B) p0030
  have p0032 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (syn_cfv H (.cv x))) (syn_csn (syn_cfv H B)) (syn_ccnv (syn_cdif S (syn_cid))) p0031
  have p0033 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))) E p0032
  have p0034 :=
    @g_id (.classEq (.cv x) B)
  have p0035 :=
    @g_fveq2d (.classEq (.cv x) B) (.cv x) B H p0034
  have p0036 :=
    @g_sneqd (.classEq (.cv x) B) (syn_cfv H (.cv x)) (syn_cfv H B) p0035
  have p0037 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (syn_cfv H (.cv x))) (syn_csn (syn_cfv H B)) (syn_ccnv (syn_cdif S (syn_cid))) p0036
  have p0038 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))) E p0037
  have p0039 :=
    @g_xpeq12d (.classEq (.cv x) B) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) p0033 p0038
  have p0040 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))) S p0039
  have p0041 :=
    @g_isoeq3 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
  have p0042 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))) (syn_wb (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) p0040 p0041
  have p0043 :=
    @g_bitrd (.classEq (.cv x) B) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) p0028 p0042
  have p0044 :=
    @g_id (.classEq (.cv x) B)
  have p0045 :=
    @g_sneqd (.classEq (.cv x) B) (.cv x) B p0044
  have p0046 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid))) p0045
  have p0047 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0046
  have p0048 :=
    @g_isoeq4 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
  have p0049 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_wb (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) p0047 p0048
  have p0050 :=
    @g_bitrd (.classEq (.cv x) B) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) p0043 p0049
  have p0051 :=
    @g_id (.classEq (.cv x) B)
  have p0052 :=
    @g_fveq2d (.classEq (.cv x) B) (.cv x) B H p0051
  have p0053 :=
    @g_sneqd (.classEq (.cv x) B) (syn_cfv H (.cv x)) (syn_cfv H B) p0052
  have p0054 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (syn_cfv H (.cv x))) (syn_csn (syn_cfv H B)) (syn_ccnv (syn_cdif S (syn_cid))) p0053
  have p0055 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))) (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))) E p0054
  have p0056 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
  have p0057 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))) (syn_wb (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) p0055 p0056
  have p0058 :=
    @g_bitrd (.classEq (.cv x) B) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))) p0050 p0057
  have p0059 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))) p0008 p0058
  have p0060 :=
    @g_isostrictsegresndv x D R S E H
  have p0061 :=
    @g_vtoclg (.imp (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) (.imp (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) x B (syn_cvv) dv_cache_0001 dv_cache_0002 p0059 p0060
  have p0062 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem B D)) (.classMem B (syn_cvv)) (.imp (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) p0003 p0061
  have p0063 :=
    @g_mpd (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))) p0000 p0062
  exact p0063

noncomputable def g_hnsiquomappreexclndv
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_hnsiquomappreexclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_chnord (syn_cpw1 A))) (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq B (syn_cfv (syn_chnsiquomap A) (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_chnord (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq B (syn_cfv (syn_chnsiquomap A) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv y) B)
  have p0001 :=
    @g_eqeq1d (.classEq (.cv y) B) (.cv y) B (syn_cfv (syn_chnsiquomap A) (.cv x)) p0000
  have p0002 :=
    @g_rexbidv (.classEq (.cv y) B) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))) (.classEq B (syn_cfv (syn_chnsiquomap A) (.cv x))) x (syn_cpw1 (syn_chnord A)) dv_cache_0001 p0001
  have p0003 :=
    @g_hnsiquomappreexndv x y A dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_hnsiquomappreexclndv_1
  have p0004 :=
    @g_vtoclga (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x)))) (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq B (syn_cfv (syn_chnsiquomap A) (.cv x)))) y B (syn_chnord (syn_cpw1 A)) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0002 p0003
  exact p0004

noncomputable def g_hnsiquomaprepvalcl2ndv
    (A : Class) (C : Class) (q : Var) (dv_A_q : q ∉ A.fv) (hyp_hnsiquomaprepvalcl2ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))) := by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ ({q} : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_ne_q : u ≠ q := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_u : q ≠ u :=
    Ne.symm fresh_u_ne_q
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ≠ u := by
    clear dv_cache_0001 dv_cache_0002
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0004 : u ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ ((Wff.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))
  have p0001 :=
    @g_simpl (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))) (.classMem C (syn_chwcn A)) p0000 p0001
  have p0003 :=
    @g_elex C (syn_chwcn A)
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_biidd (.classEq (.cv u) C) (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
  have p0006 :=
    @g_id (.classEq (.cv u) C)
  have p0007 :=
    @g_eleq1d (.classEq (.cv u) C) (.cv u) C (syn_chwcn A) p0006
  have p0008 :=
    @g_eceq1 (.cv u) C (syn_chwniso A)
  have p0009 :=
    @g_eqeq2d (.classEq (.cv u) C) (syn_cec (.cv u) (syn_chwniso A)) (syn_cec C (syn_chwniso A)) (syn_cuni (.cv q)) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv u) C) (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))) p0007 p0009
  have p0011 :=
    @g_anbi12d (.classEq (.cv u) C) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))) p0005 p0010
  have p0012 :=
    @g_id (.classEq (.cv u) C)
  have p0013 :=
    @g_sneqd (.classEq (.cv u) C) (.cv u) C p0012
  have p0014 :=
    @g_fveq2d (.classEq (.cv u) C) (syn_csn (.cv u)) (syn_csn C) (syn_chnsicodemap A) p0013
  have p0015 :=
    @g_eceq1 (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))
  have p0016 :=
    @g_syl (.classEq (.cv u) C) (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_cfv (syn_chnsicodemap A) (syn_csn C))) (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))) p0014 p0015
  have p0017 :=
    @g_eqeq2d (.classEq (.cv u) C) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))) (syn_cfv (syn_chnsiquomap A) (.cv q)) p0016
  have p0018 :=
    @g_imbi12d (.classEq (.cv u) C) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))) p0011 p0017
  have p0019 :=
    @g_hnsiquomaprepvalndv u A q dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_hnsiquomaprepvalcl2ndv_1
  have p0020 :=
    @g_vtoclg (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))))) (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))) u C (syn_cvv) dv_cache_0004 dv_cache_0005 p0018 p0019
  have p0021 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (.classMem C (syn_cvv)) (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))) p0004 p0020
  have p0022 :=
    @g_pm2_43i (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))) p0021
  exact p0022

#print axioms g_hnsiquomaprepvalcl2ndv

end NFChoice.DirectNominalPrf.WPPReplay
