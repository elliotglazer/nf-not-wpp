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
import NominalWPPReplayChunk015Compact001Part035

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

noncomputable def g_wpppowlayerseqfvcl
    (B : Class) (C : Class) (F : Class) (dv_C_F : Disjoint C.fv F.fv) (hyp_wpppowlayerseqfvcl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))) (syn_cima (syn_clec) (syn_csn C))))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : n ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.imp (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))) (syn_cima (syn_clec) (syn_csn C)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem B (syn_cnnc))
  have p0001 :=
    @g_id (.classEq (.cv n) B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0003 :=
    @g_id (.classEq (.cv n) B)
  have p0004 :=
    @g_sneqd (.classEq (.cv n) B) (.cv n) B p0003
  have p0005 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_csn (.cv n)) (syn_csn B) (syn_cwpppowlayerseq F C) p0004
  have p0006 :=
    @g_id (.classEq (.cv n) B)
  have p0007 :=
    @g_tceq (.cv n) B
  have p0008 :=
    @g_syl (.classEq (.cv n) B) (.classEq (.cv n) B) (.classEq (syn_ctc (.cv n)) (syn_ctc B)) p0006 p0007
  have p0009 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_ctc (.cv n)) (syn_ctc B) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0008
  have p0010 :=
    @g_cnveqd (.classEq (.cv n) B) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) p0009
  have p0011 :=
    @g_imaeq1d (.classEq (.cv n) B) (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))) (syn_cima (syn_clec) (syn_csn C)) p0010
  have p0012 :=
    @g_eqeq12d (.classEq (.cv n) B) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))) (syn_cima (syn_clec) (syn_csn C))) p0005 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc)) (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C)))) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))) (syn_cima (syn_clec) (syn_csn C)))) p0002 p0012
  have p0014 :=
    @g_wpppowlayerseqfv C n F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wpppowlayerseqfvcl_1
  have p0015 :=
    @g_vtoclg (.imp (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))))) (.imp (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))) (syn_cima (syn_clec) (syn_csn C))))) n B (syn_cnnc) dv_cache_0004 dv_cache_0005 p0013 p0014
  have p0016 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))) (syn_cima (syn_clec) (syn_csn C)))) p0000 p0015
  exact p0016

noncomputable def g_wpppowlayerseqsuc
    (C : Class) (n : Var) (F : Class) (dv_C_F : Disjoint C.fv F.fv) (hyp_wpppowlayerseqsuc_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv n) (syn_c1c)))) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))) := by
  let proofSupport : Finset Var := C.fv ∪ ({n} : Finset Var) ∪ F.fv
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have p0000 :=
    @g_id (.classMem (.cv n) (syn_cnnc))
  have p0001 :=
    @g_peano2 (.cv n)
  have p0002 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) p0000 p0001
  have p0003 :=
    @g_wpppowlayerseqfvcl (syn_cplc (.cv n) (syn_c1c)) C F dv_cache_0001 hyp_wpppowlayerseqsuc_1
  have p0004 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv n) (syn_c1c)))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) (syn_cima (syn_clec) (syn_csn C)))) p0002 p0003
  have p0005 :=
    @g_nntcsuc (.cv n)
  have p0006 :=
    @g_fveq2d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (syn_ctc (.cv n)) (syn_c1c)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0005
  have p0007 :=
    @g_nntccl (.cv n)
  have p0008 :=
    @g_wpppowcorersuccl (syn_ctc (.cv n)) F hyp_wpppowlayerseqsuc_1
  have p0009 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (syn_ctc (.cv n)) (syn_c1c))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F)) p0007 p0008
  have p0010 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (syn_ctc (.cv n)) (syn_c1c))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F) p0006 p0009
  have p0011 :=
    @g_cnveqd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F) p0010
  have p0012 :=
    @g_imaeq1d (.classMem (.cv n) (syn_cnnc)) (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) (syn_ccnv (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F)) (syn_cima (syn_clec) (syn_csn C)) p0011
  have p0013 :=
    @g_cnvco (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F
  have p0014 :=
    @g_a1i (.classEq (syn_ccnv (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F)) (syn_ccom (syn_ccnv F) (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))))) (.classMem (.cv n) (syn_cnnc)) p0013
  have p0015 :=
    @g_imaeq1d (.classMem (.cv n) (syn_cnnc)) (syn_ccnv (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F)) (syn_ccom (syn_ccnv F) (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))) (syn_cima (syn_clec) (syn_csn C)) p0014
  have p0016 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_ccnv (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_ccom (syn_ccnv F) (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))) (syn_cima (syn_clec) (syn_csn C))) p0012 p0015
  have p0017 :=
    @g_imaco (syn_ccnv F) (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))
  have p0018 :=
    @g_a1i (.classEq (syn_cima (syn_ccom (syn_ccnv F) (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_ccnv F) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))))) (.classMem (.cv n) (syn_cnnc)) p0017
  have p0019 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_ccom (syn_ccnv F) (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_ccnv F) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C)))) p0016 p0018
  have p0020 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv n) (syn_c1c)))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_ccnv F) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C)))) p0004 p0019
  have p0021 :=
    @g_wpppowlayerseqfvcl (.cv n) C F dv_cache_0001 hyp_wpppowlayerseqsuc_1
  have p0022 :=
    @g_eqcomd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))) p0021
  have p0023 :=
    @g_imaeq2d (.classMem (.cv n) (syn_cnnc)) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C))) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_ccnv F) p0022
  have p0024 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv n) (syn_c1c)))) (syn_cima (syn_ccnv F) (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_clec) (syn_csn C)))) (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) p0020 p0023
  exact p0024

noncomputable def g_wppreachincblayerscl
    (B : Class) (C : Class) (F : Class) (d : Var) (dv_B_d : d ∉ B.fv) (dv_C_F : Disjoint C.fv F.fv) (dv_C_d : d ∉ C.fv) (dv_F_d : d ∉ F.fv) (hyp_wppreachincblayerscl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc B))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))))))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ F.fv ∪ ({d} : Finset Var)
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_d : n ≠ d := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_n : d ≠ n :=
    Ne.symm fresh_n_ne_d
  have dv_cache_0001 : d ∉ ((Wff.classEq (.cv n) B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_n, dv_B_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint (C).fv (F).fv := by
    clear dv_cache_0001
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0003 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : d ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show d ≠ n from (by exact fresh_d_ne_n))
  have dv_cache_0008 : n ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((Wff.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc B))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, fresh_n_not_C, fresh_n_not_F, fresh_n_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem B (syn_cnnc))
  have p0001 :=
    @g_id (.classEq (.cv n) B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0003 :=
    @g_id (.classEq (.cv n) B)
  have p0004 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cwppreachincb F C) p0003
  have p0005 :=
    @g_id (.classEq (.cv n) B)
  have p0006 :=
    @g_tceq (.cv n) B
  have p0007 :=
    @g_syl (.classEq (.cv n) B) (.classEq (.cv n) B) (.classEq (syn_ctc (.cv n)) (syn_ctc B)) p0005 p0006
  have p0008 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_ctc (.cv n)) (syn_ctc B) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0007
  have p0009 :=
    @g_eleq2d (.classEq (.cv n) B) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n))) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc B)) (.cv d) p0008
  have p0010 :=
    @g_id (.classEq (.cv n) B)
  have p0011 :=
    @g_sneqd (.classEq (.cv n) B) (.cv n) B p0010
  have p0012 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_csn (.cv n)) (syn_csn B) (syn_cwpppowlayerseq F C) p0011
  have p0013 :=
    @g_eleq2d (.classEq (.cv n) B) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (.cv d) p0012
  have p0014 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc B))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))) p0009 p0013
  have p0015 :=
    @g_ralbidv (.classEq (.cv n) B) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc B))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))) d (syn_cdm F) dv_cache_0001 p0014
  have p0016 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cwppreachincb F C)) (.classMem B (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc B))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))))) p0004 p0015
  have p0017 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))))) (syn_wb (.classMem B (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc B))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))))) p0002 p0016
  have p0018 :=
    @g_wppreachincblayers C n F d dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_wppreachincblayerscl_1
  have p0019 :=
    @g_vtoclg (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv n)))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))))) (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc B))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))))))) n B (syn_cnnc) dv_cache_0008 dv_cache_0009 p0017 p0018
  have p0020 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc B))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))))) p0000 p0019
  exact p0020

#print axioms g_wppreachincblayerscl

end NFChoice.DirectNominalPrf.WPPReplay
