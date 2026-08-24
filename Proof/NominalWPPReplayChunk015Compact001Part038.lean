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
import NominalWPPReplayChunk015Compact001Part037

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

noncomputable def g_wppreachlayerorbfin
    (C : Class) (D : Class) (F : Class) (N : Class) (dv_C_F : Disjoint C.fv F.fv) (hyp_wppreachlayerorbfin_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachlayerorbfin_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wppreachlayerorbfin_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv ∪ N.fv
  let e : Var := freshVar proofSupport 0
  have fresh_e : e ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_e_not_D : e ∉ D.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_e_not_F : e ∉ F.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e_not_N : e ∉ N.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : e ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : e ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : e ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : e ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : e ∉ ((syn_cdm F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : e ∉ ((syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_D, fresh_e_not_N, fresh_e_not_F, fresh_e_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_a1i (.classMem D (syn_cdm F)) (.classMem N (syn_cnnc)) hyp_wppreachlayerorbfin_2
  have p0001 :=
    @g_wppreachpowlayers C F N e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_wppreachlayerorbfin_1 hyp_wppreachlayerorbfin_3
  have p0002 :=
    @g_jca (.classMem N (syn_cnnc)) (.classMem D (syn_cdm F)) (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))))) p0000 p0001
  have p0003 :=
    @g_id (.classEq (.cv e) D)
  have p0004 :=
    @g_eleq1d (.classEq (.cv e) D) (.cv e) D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N)) p0003
  have p0005 :=
    @g_id (.classEq (.cv e) D)
  have p0006 :=
    @g_eleq1d (.classEq (.cv e) D) (.cv e) D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)) p0005
  have p0007 :=
    @g_bibi12d (.classEq (.cv e) D) (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))) p0004 p0006
  have p0008 :=
    @g_rspcva (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))) (syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))) e D (syn_cdm F) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0007
  have p0009 :=
    @g_syl (.classMem N (syn_cnnc)) (syn_wa (.classMem D (syn_cdm F)) (syn_wral e (syn_cdm F) (syn_wb (.classMem (.cv e) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem (.cv e) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))))) (syn_wb (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N)))) p0002 p0008
  have p0010 :=
    @g_wpppowlayerorbcl N C D F dv_cache_0001 hyp_wppreachlayerorbfin_1 hyp_wppreachlayerorbfin_2 hyp_wppreachlayerorbfin_3
  have p0011 :=
    @g_bitrd (.classMem N (syn_cnnc)) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc N))) (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)) p0009 p0010
  exact p0011

noncomputable def g_strictsegdifinindv
    (x : Var) (D : Class) (R : Class) :
    Nominal.NPrf (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elstrictseg x y D R
  have p0001 :=
    @g_eldifsn (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (.cv x)
  have p0002 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))
  have p0003 :=
    @g_eliniseg R (.cv x) (.cv y)
  have p0004 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_wbr (.cv y) R (.cv x)) (.classMem (.cv y) D) p0003
  have p0005 :=
    @g_bitri (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (.classMem (.cv y) (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x))) p0002 p0004
  have p0006 :=
    @g_anbi1i (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x))) (syn_wne (.cv y) (.cv x)) p0005
  have p0007 :=
    @g_bitri (.classMem (.cv y) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_wa (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_wne (.cv y) (.cv x))) (syn_wa (syn_wa (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x))) (syn_wne (.cv y) (.cv x))) p0001 p0006
  have p0008 :=
    @g_anass (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))
  have p0009 :=
    @g_bitri (.classMem (.cv y) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_wa (syn_wa (.classMem (.cv y) D) (syn_wbr (.cv y) R (.cv x))) (syn_wne (.cv y) (.cv x))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0007 p0008
  have p0010 :=
    @g_bitr4i (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) (.classMem (.cv y) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))) p0000 p0009
  have p0011 :=
    @g_eqriv y (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) dv_cache_0001 dv_cache_0002 p0010
  exact p0011

#print axioms g_strictsegdifinindv

end NFChoice.DirectNominalPrf.WPPReplay
