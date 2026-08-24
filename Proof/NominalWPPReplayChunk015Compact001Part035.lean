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
import NominalWPPReplayChunk015Compact001Part034

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

noncomputable def g_wpppreimaactsnd
    (ph : Wff) (D : Class) (R : Class) (U : Class) (O : Class) (hyp_wpppreimaactsnd_1 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_wpppreimaactsnd_2 : Nominal.NPrf (.classMem O (syn_cvv))) (hyp_wpppreimaactsnd_3 : Nominal.NPrf (.imp ph (.classEq (syn_cima R (syn_csn D)) (syn_csn O)))) :
    Nominal.NPrf (.imp ph (syn_wb (.classMem D (syn_cima (syn_ccnv R) U)) (.classMem O U))) := by
  let proofSupport : Finset Var := ph.fv ∪ D.fv ∪ R.fv ∪ U.fv ∪ O.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_U : x ∉ U.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_O : x ∉ O.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ccnv R)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (U).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_U, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (O).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_O, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classMem O U)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_O, fresh_x_not_U, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elima x D (syn_ccnv R) U dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_a1i (syn_wb (.classMem D (syn_cima (syn_ccnv R) U)) (syn_wrex x U (syn_wbr (.cv x) (syn_ccnv R) D))) ph p0000
  have p0002 :=
    @g_brcnv (.cv x) D R
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr D R (.cv x))))
  have p0004 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv R) D) (syn_wbr D R (.cv x)) (.classMem (syn_cop D (.cv x)) R) p0002 p0003
  have p0005 :=
    @g_elimasn R D (.cv x)
  have p0006 :=
    @g_bicomi (.classMem (.cv x) (syn_cima R (syn_csn D))) (.classMem (syn_cop D (.cv x)) R) p0005
  have p0007 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv R) D) (.classMem (syn_cop D (.cv x)) R) (.classMem (.cv x) (syn_cima R (syn_csn D))) p0004 p0006
  have p0008 :=
    @g_a1i (syn_wb (syn_wbr (.cv x) (syn_ccnv R) D) (.classMem (.cv x) (syn_cima R (syn_csn D)))) ph p0007
  have p0009 :=
    @g_eleq2d ph (syn_cima R (syn_csn D)) (syn_csn O) (.cv x) hyp_wpppreimaactsnd_3
  have p0010 :=
    @g_bitrd ph (syn_wbr (.cv x) (syn_ccnv R) D) (.classMem (.cv x) (syn_cima R (syn_csn D))) (.classMem (.cv x) (syn_csn O)) p0008 p0009
  have p0011 :=
    @g_rexbidv ph (syn_wbr (.cv x) (syn_ccnv R) D) (.classMem (.cv x) (syn_csn O)) x U dv_cache_0004 p0010
  have p0012 :=
    @g_bitrd ph (.classMem D (syn_cima (syn_ccnv R) U)) (syn_wrex x U (syn_wbr (.cv x) (syn_ccnv R) D)) (syn_wrex x U (.classMem (.cv x) (syn_csn O))) p0001 p0011
  have p0013 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x U (.classMem (.cv x) (syn_csn O)))))
  have p0014 :=
    @g_ancom (.classMem (.cv x) U) (.classMem (.cv x) (syn_csn O))
  have p0015 :=
    @g_exbii (syn_wa (.classMem (.cv x) U) (.classMem (.cv x) (syn_csn O))) (syn_wa (.classMem (.cv x) (syn_csn O)) (.classMem (.cv x) U)) x p0014
  have p0016 :=
    @g_bitri (syn_wrex x U (.classMem (.cv x) (syn_csn O))) (syn_wex x (syn_wa (.classMem (.cv x) U) (.classMem (.cv x) (syn_csn O)))) (syn_wex x (syn_wa (.classMem (.cv x) (syn_csn O)) (.classMem (.cv x) U))) p0013 p0015
  have p0017 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x (syn_csn O) (.classMem (.cv x) U))))
  have p0018 :=
    @g_bicomi (syn_wrex x (syn_csn O) (.classMem (.cv x) U)) (syn_wex x (syn_wa (.classMem (.cv x) (syn_csn O)) (.classMem (.cv x) U))) p0017
  have p0019 :=
    @g_bitri (syn_wrex x U (.classMem (.cv x) (syn_csn O))) (syn_wex x (syn_wa (.classMem (.cv x) (syn_csn O)) (.classMem (.cv x) U))) (syn_wrex x (syn_csn O) (.classMem (.cv x) U)) p0016 p0018
  have p0020 :=
    @g_id (.classEq (.cv x) O)
  have p0021 :=
    @g_eleq1d (.classEq (.cv x) O) (.cv x) O U p0020
  have p0022 :=
    @g_rexsn (.classMem (.cv x) U) (.classMem O U) x O dv_cache_0005 dv_cache_0006 hyp_wpppreimaactsnd_2 p0021
  have p0023 :=
    @g_bitri (syn_wrex x U (.classMem (.cv x) (syn_csn O))) (syn_wrex x (syn_csn O) (.classMem (.cv x) U)) (.classMem O U) p0019 p0022
  have p0024 :=
    @g_a1i (syn_wb (syn_wrex x U (.classMem (.cv x) (syn_csn O))) (.classMem O U)) ph p0023
  have p0025 :=
    @g_bitrd ph (.classMem D (syn_cima (syn_ccnv R) U)) (syn_wrex x U (.classMem (.cv x) (syn_csn O))) (.classMem O U) p0012 p0024
  exact p0025

noncomputable def g_wpppowlayerorb
    (C : Class) (D : Class) (n : Var) (F : Class) (dv_C_F : Disjoint C.fv F.fv) (dv_C_n : n ∉ C.fv) (dv_F_n : n ∉ F.fv) (hyp_wpppowlayerorb_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wpppowlayerorb_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wpppowlayerorb_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ ({n} : Finset Var) ∪ F.fv
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : n ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex F (syn_cfuns)
  have p0001 :=
    Nominal.mp hyp_wpppowlayerorb_1 p0000
  have p0002 :=
    @g_wpppowlayerseqfv C n F dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @g_eleq2d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))) D p0002
  have p0004 :=
    @g_elex D (syn_cdm F)
  have p0005 :=
    Nominal.mp hyp_wpppowlayerorb_2 p0004
  have p0006 :=
    @g_fvex (.cv n) (syn_cfrec F D)
  have p0007 :=
    @g_wpppowatact D F (.cv n) hyp_wpppowlayerorb_1 hyp_wpppowlayerorb_2 hyp_wpppowlayerorb_3
  have p0008 :=
    @g_wpppreimaactsnd (.classMem (.cv n) (syn_cnnc)) D (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_cima (syn_clec) (syn_csn C)) (syn_cfv (syn_cfrec F D) (.cv n)) p0005 p0006 p0007
  have p0009 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) (.classMem D (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C)))) (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cima (syn_clec) (syn_csn C))) p0003 p0008
  have p0010 :=
    @g_elimasn (syn_clec) C (syn_cfv (syn_cfrec F D) (.cv n))
  have p0011 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))))
  have p0012 :=
    @g_bicomi (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) (.classMem (syn_cop C (syn_cfv (syn_cfrec F D) (.cv n))) (syn_clec)) p0011
  have p0013 :=
    @g_bitri (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cima (syn_clec) (syn_csn C))) (.classMem (syn_cop C (syn_cfv (syn_cfrec F D) (.cv n))) (syn_clec)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) p0010 p0012
  have p0014 :=
    @g_a1i (syn_wb (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cima (syn_clec) (syn_csn C))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) p0013
  have p0015 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cima (syn_clec) (syn_csn C))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) p0009 p0014
  exact p0015

noncomputable def g_wppprecompex
    (F : Class) (hyp_wppprecompex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppprecomp F) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    (by simpa [syn_cwppprecomp] using (Nominal.classEqRefl (syn_cwppprecomp F)))
  have p0001 :=
    @g_composeex
  have p0002 :=
    @g_idex
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_snex F
  have p0005 :=
    @g_xpex (syn_cvv) (syn_csn F) p0003 p0004
  have p0006 :=
    @g_txpex (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)) p0002 p0005
  have p0007 :=
    @g_coex (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) p0001 p0006
  have p0008 :=
    @g_eqeltri (syn_cwppprecomp F) (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) (syn_cvv) p0000 p0007
  exact p0008

noncomputable def g_wppprecompfn
    (F : Class) (hyp_wppprecompfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwppprecomp F) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    @g_composefn
  have p0001 :=
    @g_f1ovi
  have p0002 :=
    @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0005 :=
    Nominal.mp hyp_wppprecompfn_1 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) p0003 p0005
  have p0007 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_inidm (syn_cvv)
  have p0010 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) p0009
  have p0011 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_fncovv (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) p0000 p0011
  have p0013 :=
    (by simpa [syn_cwppprecomp] using (Nominal.classEqRefl (syn_cwppprecomp F)))
  have p0014 :=
    @g_fneq1i (syn_cvv) (syn_cwppprecomp F) (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) p0013
  have p0015 :=
    @g_mpbir (syn_wfn (syn_cwppprecomp F) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) (syn_cvv)) p0012 p0014
  exact p0015

noncomputable def g_wppprecompfv
    (R : Class) (F : Class) (hyp_wppprecompfv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wppprecompfv_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppprecomp F) R) (syn_ccom R F)) := by
  let proofSupport : Finset Var := R.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwppprecomp] using (Nominal.classEqRefl (syn_cwppprecomp F)))
  have p0001 :=
    @g_fveq1i R (syn_cwppprecomp F) (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) p0000
  have p0002 :=
    @g_f1ovi
  have p0003 :=
    @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0006 :=
    Nominal.mp hyp_wppprecompfv_1 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_inidm (syn_cvv)
  have p0011 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) p0010
  have p0012 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) (syn_cvv)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) (syn_cvv)) (.classMem R (syn_cvv)) p0012 hyp_wppprecompfv_2
  have p0014 :=
    @g_fvco2 (syn_cvv) R (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_f1ovi
  have p0017 :=
    @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0020 :=
    Nominal.mp hyp_wppprecompfv_1 p0019
  have p0021 :=
    @g_fvtxpvv R (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)) p0018 p0020 hyp_wppprecompfv_2
  have p0022 :=
    @g_fvi R (syn_cvv)
  have p0023 :=
    Nominal.mp hyp_wppprecompfv_2 p0022
  have p0024 :=
    @g_fvconst2 (syn_cvv) F R hyp_wppprecompfv_1
  have p0025 :=
    Nominal.mp hyp_wppprecompfv_2 p0024
  have p0026 :=
    @g_opeq12i (syn_cfv (syn_cid) R) R (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) R) F p0023 p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) R) (syn_cop (syn_cfv (syn_cid) R) (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) R)) (syn_cop R F) p0021 p0026
  have p0028 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) R) (syn_cop R F) (syn_ccompose) p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) R) (syn_cfv (syn_ccompose) (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) R)) (syn_cfv (syn_ccompose) (syn_cop R F)) p0015 p0028
  have p0030 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co R (syn_ccompose) F)))
  have p0031 :=
    @g_eqcomi (syn_co R (syn_ccompose) F) (syn_cfv (syn_ccompose) (syn_cop R F)) p0030
  have p0032 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) R) (syn_cfv (syn_ccompose) (syn_cop R F)) (syn_co R (syn_ccompose) F) p0029 p0031
  have p0033 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem F (syn_cvv)) hyp_wppprecompfv_2 hyp_wppprecompfv_1
  have p0034 :=
    @g_composevalg R F (syn_cvv) (syn_cvv)
  have p0035 :=
    Nominal.mp p0033 p0034
  have p0036 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) R) (syn_co R (syn_ccompose) F) (syn_ccom R F) p0032 p0035
  have p0037 :=
    @g_eqtri (syn_cfv (syn_cwppprecomp F) R) (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) R) (syn_ccom R F) p0001 p0036
  exact p0037

noncomputable def g_wpppowcommeqex
    (F : Class) (hyp_wpppowcommeqex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppowcommeq F) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    (by simpa [syn_cwpppowcommeq] using (Nominal.classEqRefl (syn_cwpppowcommeq F)))
  have p0001 :=
    @g_wppprecompex F hyp_wpppowcommeqex_1
  have p0002 :=
    @g_eqid (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0003 :=
    @g_wpppostcompex F hyp_wpppowcommeqex_1
  have p0004 :=
    @g_frecex (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cwpppostcomp F) (syn_cid) p0002 p0003
  have p0005 :=
    @g_coex (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0001 p0004
  have p0006 :=
    @g_cnvex (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) p0005
  have p0007 :=
    @g_wpppostcompex F hyp_wpppowcommeqex_1
  have p0008 :=
    @g_eqid (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0009 :=
    @g_wpppostcompex F hyp_wpppowcommeqex_1
  have p0010 :=
    @g_frecex (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cwpppostcomp F) (syn_cid) p0008 p0009
  have p0011 :=
    @g_coex (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0007 p0010
  have p0012 :=
    @g_coex (syn_ccnv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) p0006 p0011
  have p0013 :=
    @g_fixex (syn_ccom (syn_ccnv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) p0012
  have p0014 :=
    @g_eqeltri (syn_cwpppowcommeq F) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))) (syn_cvv) p0000 p0013
  exact p0014

noncomputable def g_wpppowcommeqval
    (n : Var) (F : Class) (hyp_wpppowcommeqval_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))))) := by
  let proofSupport : Finset Var := ({n} : Finset Var) ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpppowcommeq] using (Nominal.classEqRefl (syn_cwpppowcommeq F)))
  have p0001 :=
    @g_eleq2i (syn_cwpppowcommeq F) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))) (.cv n) p0000
  have p0002 :=
    @g_a1i (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classMem (.cv n) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))))) (.classMem (.cv n) (syn_cnnc)) p0001
  have p0003 :=
    @g_wppprecompfn F hyp_wpppowcommeqval_1
  have p0004 :=
    @g_wpppowcorefn F hyp_wpppowcommeqval_1
  have p0005 :=
    @g_ssv (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0006 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwppprecomp F) (syn_cvv)) (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (syn_wss (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cvv)) p0003 p0004 p0005
  have p0007 :=
    @g_fnco (syn_cvv) (syn_cnnc) (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_fnfun (syn_cnnc) (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_a1i (syn_wfun (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (.classMem (.cv n) (syn_cnnc)) p0010
  have p0012 :=
    @g_wpppostcompfn F hyp_wpppowcommeqval_1
  have p0013 :=
    @g_wpppowcorefn F hyp_wpppowcommeqval_1
  have p0014 :=
    @g_ssv (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0015 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwpppostcomp F) (syn_cvv)) (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (syn_wss (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cvv)) p0012 p0013 p0014
  have p0016 :=
    @g_fnco (syn_cvv) (syn_cnnc) (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_fnfun (syn_cnnc) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_a1i (syn_wfun (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (.classMem (.cv n) (syn_cnnc)) p0019
  have p0021 :=
    @g_id (.classMem (.cv n) (syn_cnnc))
  have p0022 :=
    @g_wppprecompfn F hyp_wpppowcommeqval_1
  have p0023 :=
    @g_wpppowcorefn F hyp_wpppowcommeqval_1
  have p0024 :=
    @g_ssv (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0025 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwppprecomp F) (syn_cvv)) (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (syn_wss (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cvv)) p0022 p0023 p0024
  have p0026 :=
    @g_fnco (syn_cvv) (syn_cnnc) (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_fndm (syn_cnnc) (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_a1i (.classEq (syn_cdm (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) p0029
  have p0031 :=
    @g_eleqtrrd (.classMem (.cv n) (syn_cnnc)) (.cv n) (syn_cnnc) (syn_cdm (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) p0021 p0030
  have p0032 :=
    @g_id (.classMem (.cv n) (syn_cnnc))
  have p0033 :=
    @g_wpppostcompfn F hyp_wpppowcommeqval_1
  have p0034 :=
    @g_wpppowcorefn F hyp_wpppowcommeqval_1
  have p0035 :=
    @g_ssv (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0036 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwpppostcomp F) (syn_cvv)) (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (syn_wss (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cvv)) p0033 p0034 p0035
  have p0037 :=
    @g_fnco (syn_cvv) (syn_cnnc) (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_fndm (syn_cnnc) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_a1i (.classEq (syn_cdm (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) p0040
  have p0042 :=
    @g_eleqtrrd (.classMem (.cv n) (syn_cnnc)) (.cv n) (syn_cnnc) (syn_cdm (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) p0032 p0041
  have p0043 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cdm (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))) (.classMem (.cv n) (syn_cdm (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))) p0031 p0042
  have p0044 :=
    @g_n_3jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_wfun (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_wa (.classMem (.cv n) (syn_cdm (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))) (.classMem (.cv n) (syn_cdm (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))) p0011 p0020 p0043
  have p0045 :=
    @g_funeqfix (.cv n) (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0046 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_w3a (syn_wfun (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_wfun (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_wa (.classMem (.cv n) (syn_cdm (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))) (.classMem (.cv n) (syn_cdm (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))))) (syn_wb (.classMem (.cv n) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))) (.classEq (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)) (syn_cfv (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)))) p0044 p0045
  have p0047 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classMem (.cv n) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))) (.classEq (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)) (syn_cfv (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n))) p0002 p0046
  have p0048 :=
    @g_wpppowcorefn F hyp_wpppowcommeqval_1
  have p0049 :=
    @g_a1i (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) p0048
  have p0050 :=
    @g_id (.classMem (.cv n) (syn_cnnc))
  have p0051 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) p0049 p0050
  have p0052 :=
    @g_fvco2 (syn_cnnc) (.cv n) (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0053 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (.classEq (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)) (syn_cfv (syn_cwppprecomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))) p0051 p0052
  have p0054 :=
    @g_fvex (.cv n) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0055 :=
    @g_wppprecompfv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F hyp_wpppowcommeqval_1 p0054
  have p0056 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppprecomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F)) (.classMem (.cv n) (syn_cnnc)) p0055
  have p0057 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)) (syn_cfv (syn_cwppprecomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F) p0053 p0056
  have p0058 :=
    @g_wpppowcorefn F hyp_wpppowcommeqval_1
  have p0059 :=
    @g_a1i (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) p0058
  have p0060 :=
    @g_id (.classMem (.cv n) (syn_cnnc))
  have p0061 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) p0059 p0060
  have p0062 :=
    @g_fvco2 (syn_cnnc) (.cv n) (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0063 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (.classEq (syn_cfv (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)) (syn_cfv (syn_cwpppostcomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))) p0061 p0062
  have p0064 :=
    @g_fvex (.cv n) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0065 :=
    @g_wpppostcompfv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F hyp_wpppowcommeqval_1 p0064
  have p0066 :=
    @g_a1i (.classEq (syn_cfv (syn_cwpppostcomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) p0065
  have p0067 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)) (syn_cfv (syn_cwpppostcomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) p0063 p0066
  have p0068 :=
    @g_eqeq12d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F) (syn_cfv (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) p0057 p0067
  have p0069 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classEq (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)) (syn_cfv (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n))) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))) p0047 p0068
  exact p0069

noncomputable def g_wpppowcommeqvalcl
    (B : Class) (F : Class) (hyp_wpppowcommeqvalcl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))))) := by
  let proofSupport : Finset Var := B.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : n ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((Wff.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem B (syn_cnnc))
  have p0001 :=
    @g_id (.classEq (.cv n) B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0003 :=
    @g_id (.classEq (.cv n) B)
  have p0004 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cwpppowcommeq F) p0003
  have p0005 :=
    @g_id (.classEq (.cv n) B)
  have p0006 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0005
  have p0007 :=
    @g_coeq1d (.classEq (.cv n) B) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F p0006
  have p0008 :=
    @g_id (.classEq (.cv n) B)
  have p0009 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0008
  have p0010 :=
    @g_coeq2d (.classEq (.cv n) B) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F p0009
  have p0011 :=
    @g_eqeq12d (.classEq (.cv n) B) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)) p0007 p0010
  have p0012 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classMem B (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))) p0004 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))) (syn_wb (.classMem B (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))) p0002 p0012
  have p0014 :=
    @g_wpppowcommeqval n F hyp_wpppowcommeqvalcl_1
  have p0015 :=
    @g_vtoclg (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))))) (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))))) n B (syn_cnnc) dv_cache_0001 dv_cache_0002 p0013 p0014
  have p0016 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))) p0000 p0015
  exact p0016

noncomputable def g_wpppowcommall
    (F : Class) (N : Class) (hyp_wpppowcommall_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem N (syn_cwpppowcommeq F))) := by
  let proofSupport : Finset Var := F.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (h))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have dv_cache_0001 : n ∉ ((syn_cwpppowcommeq F)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : m ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((Wff.classMem (.cv m) (syn_cwpppowcommeq F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((Wff.classMem (.cv n) (syn_cwpppowcommeq F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((Wff.classMem (syn_c0c) (syn_cwpppowcommeq F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.classMem N (syn_cwpppowcommeq F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((Wff.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have p0000 :=
    @g_wpppowcommeqex F hyp_wpppowcommall_1
  have p0001 :=
    @g_abid2 n (syn_cwpppowcommeq F) dv_cache_0001
  have p0002 :=
    @g_eleq1i (.cab n (.classMem (.cv n) (syn_cwpppowcommeq F))) (syn_cwpppowcommeq F) (syn_cvv) p0001
  have p0003 :=
    @g_mpbir (.classMem (.cab n (.classMem (.cv n) (syn_cwpppowcommeq F))) (syn_cvv)) (.classMem (syn_cwpppowcommeq F) (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_id (.classEq (.cv n) (syn_c0c))
  have p0005 :=
    @g_eleq1d (.classEq (.cv n) (syn_c0c)) (.cv n) (syn_c0c) (syn_cwpppowcommeq F) p0004
  have p0006 :=
    @g_id (.classEq (.cv n) (.cv m))
  have p0007 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (syn_cwpppowcommeq F) p0006
  have p0008 :=
    @g_id (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
  have p0009 :=
    @g_eleq1d (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F) p0008
  have p0010 :=
    @g_id (.classEq (.cv n) N)
  have p0011 :=
    @g_eleq1d (.classEq (.cv n) N) (.cv n) N (syn_cwpppowcommeq F) p0010
  have p0012 :=
    @g_wpppowcore0 F hyp_wpppowcommall_1
  have p0013 :=
    @g_coeq1i (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid) F p0012
  have p0014 :=
    @g_coi2 F
  have p0015 :=
    @g_eqtri (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) F) (syn_ccom (syn_cid) F) F p0013 p0014
  have p0016 :=
    @g_wpppowcore0 F hyp_wpppowcommall_1
  have p0017 :=
    @g_coeq2i (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid) F p0016
  have p0018 :=
    @g_coi1 F
  have p0019 :=
    @g_eqtri (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c))) (syn_ccom F (syn_cid)) F p0017 p0018
  have p0020 :=
    @g_eqcomi (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c))) F p0019
  have p0021 :=
    @g_eqtri (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) F) F (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c))) p0015 p0020
  have p0022 :=
    @g_peano1
  have p0023 :=
    @g_wpppowcommeqvalcl (syn_c0c) F hyp_wpppowcommall_1
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)))) p0021 p0024
  have p0026 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))
  have p0027 :=
    @g_wpppowcoresuc m F dv_cache_0002 hyp_wpppowcommall_1
  have p0028 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)))) p0026 p0027
  have p0029 :=
    @g_coeq1d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) F p0028
  have p0030 :=
    @g_coass F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F
  have p0031 :=
    @g_a1i (.classEq (syn_ccom (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) F) (syn_ccom F (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) p0030
  have p0032 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F) (syn_ccom (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) F) (syn_ccom F (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F)) p0029 p0031
  have p0033 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))
  have p0034 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))
  have p0035 :=
    @g_wpppowcommeqval m F hyp_wpppowcommall_1
  have p0036 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (.classMem (.cv m) (syn_cnnc)) (syn_wb (.classMem (.cv m) (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))))) p0034 p0035
  have p0037 :=
    @g_biimpd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (.classMem (.cv m) (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)))) p0036
  have p0038 :=
    @g_mpd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (.classMem (.cv m) (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)))) p0033 p0037
  have p0039 :=
    @g_coeq2d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) F p0038
  have p0040 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F) (syn_ccom F (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F)) (syn_ccom F (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)))) p0032 p0039
  have p0041 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))
  have p0042 :=
    @g_wpppowcoresuc m F dv_cache_0002 hyp_wpppowcommall_1
  have p0043 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)))) p0041 p0042
  have p0044 :=
    @g_eqcomd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) p0043
  have p0045 :=
    @g_coeq2d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F p0044
  have p0046 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F) (syn_ccom F (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c)))) p0040 p0045
  have p0047 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))
  have p0048 :=
    @g_peano2 (.cv m)
  have p0049 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) p0047 p0048
  have p0050 :=
    @g_wpppowcommeqvalcl (syn_cplc (.cv m) (syn_c1c)) F hyp_wpppowcommall_1
  have p0051 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (syn_wb (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c)))))) p0049 p0050
  have p0052 :=
    @g_mpbird (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))))) p0046 p0051
  have p0053 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F)) p0052
  have p0054_e02_recanon : Nominal.NPrf (.imp (.objEq n m) (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classMem (.cv m) (syn_cwpppowcommeq F)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpppowcommeq syn_cfix syn_crn syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_cvv syn_cin syn_cid syn_copab syn_ccom syn_ccnv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0054 :=
    @g_finds (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classMem (syn_c0c) (syn_cwpppowcommeq F)) (.classMem (.cv m) (syn_cwpppowcommeq F)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F)) (.classMem N (syn_cwpppowcommeq F)) n m N dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0003 p0005 p0054_e02_recanon p0009 p0011 p0025 p0053
  exact p0054

noncomputable def g_wpppowcomm
    (B : Class) (F : Class) (hyp_wpppowcomm_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))) := by
  let proofSupport : Finset Var := B.fv ∪ F.fv
  have p0000 :=
    @g_wpppowcommall F B hyp_wpppowcomm_1
  have p0001 :=
    @g_wpppowcommeqvalcl B F hyp_wpppowcomm_1
  have p0002 :=
    @g_mpbid (.classMem B (syn_cnnc)) (.classMem B (syn_cwpppowcommeq F)) (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))) p0000 p0001
  exact p0002

noncomputable def g_wpppowcorersuccl
    (B : Class) (F : Class) (hyp_wpppowcorersuccl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F))) := by
  let proofSupport : Finset Var := B.fv ∪ F.fv
  have p0000 :=
    @g_wpppowcoresuccl B F hyp_wpppowcorersuccl_1
  have p0001 :=
    @g_wpppowcomm B F hyp_wpppowcorersuccl_1
  have p0002 :=
    @g_eqcomd (.classMem B (syn_cnnc)) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)) p0001
  have p0003 :=
    @g_eqtrd (.classMem B (syn_cnnc)) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) p0000 p0002
  exact p0003

#print axioms g_wpppowcorersuccl

end NFChoice.DirectNominalPrf.WPPReplay
