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
import NominalWPPReplayChunk017Compact001Part055

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

noncomputable def g_wppreachtchwboundedndv
    (x : Var) (C : Class) (F : Class) (G : Class) (r : Var) (p : Var) (d : Var) (dv_C_p : p ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_G_p : p ∉ G.fv) (dv_G_r : r ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_d_p : d ≠ p) (dv_d_r : d ≠ r) (dv_d_x : d ≠ x) (dv_p_r : p ≠ r) (dv_p_x : p ≠ x) (dv_r_x : r ≠ x) (hyp_wppreachtchwboundedndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachtchwboundedndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppreachtchwboundedndv_3 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppreachtchwboundedndv_4 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppreachtchwboundedndv_5 : Nominal.NPrf (syn_wral x (syn_cdm F) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x)))))) (hyp_wppreachtchwboundedndv_6 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G)))))) (hyp_wppreachtchwboundedndv_7 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs)))))) (hyp_wppreachtchwboundedndv_8 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wb (.classMem (.cv d) (syn_cwppreach F C)) (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ F.fv ∪ G.fv ∪ ({r} : Finset Var) ∪ ({p} : Finset Var) ∪ ({d} : Finset Var)
  have dv_cache_0001 : p ∉ ((syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_d_p), dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wa (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_d_p), dv_C_p, dv_F_p, dv_G_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((Wff.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_p_r), (Ne.symm dv_d_r), dv_C_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r)) (syn_cncs))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_d_p), dv_C_p, dv_p_r, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_d_r), dv_C_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_d_x), dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
  have p0001 :=
    @g_eleq1d (.classEq (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cwppreach F C) p0000
  have p0002 :=
    @g_tceq (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
  have p0003 :=
    @g_eleq1d (.classEq (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_ctc (.cv d)) (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cwppreach G (syn_ctc C)) p0002
  have p0004 :=
    @g_bibi12d (.classEq (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.classMem (.cv d) (syn_cwppreach F C)) (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cwppreach F C)) (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cwppreach G (syn_ctc C))) p0001 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0006 :=
    @g_iftrue (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C
  have p0007 :=
    @g_breq1d (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (.cv d) C (syn_clec) p0006
  have p0008 :=
    @g_mpbird (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wbr (.cv d) (syn_clec) C) p0005 p0007
  have p0009 :=
    @g_hwcardssnc (syn_cvv)
  have p0010 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0009
  have p0011 :=
    Nominal.mp hyp_wppreachtchwboundedndv_8 p0010
  have p0012 :=
    @g_nclecid C
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_a1i (syn_wbr C (syn_clec) C) (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) p0013
  have p0015 :=
    @g_iffalse (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C
  have p0016 :=
    @g_breq1d (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) C C (syn_clec) p0015
  have p0017 :=
    @g_mpbird (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wbr C (syn_clec) C) p0014 p0016
  have p0018 :=
    @g_pm2_61i (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) p0008 p0017
  have p0019 :=
    @g_tru
  have p0020 :=
    @g_simpr syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
  have p0021 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0022 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0020 p0021
  have p0023 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)))) hyp_wppreachtchwboundedndv_8
  have p0024 :=
    @g_ifclda syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C (syn_chwcards (syn_cvv)) p0022 p0023
  have p0025 :=
    Nominal.mp p0019 p0024
  have p0026 :=
    @g_pm3_2i (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G))))) p0025 hyp_wppreachtchwboundedndv_6
  have p0027 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
  have p0028 :=
    @g_breq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) C (syn_clec) p0027
  have p0029 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
  have p0030 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F) p0029
  have p0031 :=
    @g_tceq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
  have p0032 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_ctc (.cv p)) (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G) p0031
  have p0033 :=
    @g_anbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G)) p0030 p0032
  have p0034 :=
    @g_imbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G))) (syn_wa (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))) p0028 p0033
  have p0035 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G)))) (.imp (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wa (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G)))) p (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0034
  have p0036 :=
    Nominal.mp p0026 p0035
  have p0037 :=
    Nominal.mp p0018 p0036
  have p0038 :=
    @g_simpl (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_simpr (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0041 :=
    @g_iftrue (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C
  have p0042 :=
    @g_breq1d (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (.cv d) C (syn_clec) p0041
  have p0043 :=
    @g_mpbird (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wbr (.cv d) (syn_clec) C) p0040 p0042
  have p0044 :=
    @g_hwcardssnc (syn_cvv)
  have p0045 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0044
  have p0046 :=
    Nominal.mp hyp_wppreachtchwboundedndv_8 p0045
  have p0047 :=
    @g_nclecid C
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_a1i (syn_wbr C (syn_clec) C) (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) p0048
  have p0050 :=
    @g_iffalse (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C
  have p0051 :=
    @g_breq1d (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) C C (syn_clec) p0050
  have p0052 :=
    @g_mpbird (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wbr C (syn_clec) C) p0049 p0051
  have p0053 :=
    @g_pm2_61i (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) p0043 p0052
  have p0054 :=
    @g_tru
  have p0055 :=
    @g_simpr syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
  have p0056 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0057 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0055 p0056
  have p0058 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)))) hyp_wppreachtchwboundedndv_8
  have p0059 :=
    @g_ifclda syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C (syn_chwcards (syn_cvv)) p0057 p0058
  have p0060 :=
    Nominal.mp p0054 p0059
  have p0061 :=
    @g_pm3_2i (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G))))) p0060 hyp_wppreachtchwboundedndv_6
  have p0062 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
  have p0063 :=
    @g_breq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) C (syn_clec) p0062
  have p0064 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
  have p0065 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F) p0064
  have p0066 :=
    @g_tceq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
  have p0067 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_ctc (.cv p)) (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G) p0066
  have p0068 :=
    @g_anbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G)) p0065 p0067
  have p0069 :=
    @g_imbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G))) (syn_wa (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))) p0063 p0068
  have p0070 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G)))) (.imp (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wa (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G)))) p (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0069
  have p0071 :=
    Nominal.mp p0061 p0070
  have p0072 :=
    Nominal.mp p0053 p0071
  have p0073 :=
    @g_simpr (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))
  have p0074 :=
    Nominal.mp p0072 p0073
  have p0075 :=
    @g_hwcardssnc (syn_cvv)
  have p0076 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0075
  have p0077 :=
    Nominal.mp hyp_wppreachtchwboundedndv_8 p0076
  have p0078 :=
    @g_simpr (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0079 :=
    @g_iftrue (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C
  have p0080 :=
    @g_breq1d (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (.cv d) C (syn_clec) p0079
  have p0081 :=
    @g_mpbird (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wbr (.cv d) (syn_clec) C) p0078 p0080
  have p0082 :=
    @g_hwcardssnc (syn_cvv)
  have p0083 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0082
  have p0084 :=
    Nominal.mp hyp_wppreachtchwboundedndv_8 p0083
  have p0085 :=
    @g_nclecid C
  have p0086 :=
    Nominal.mp p0084 p0085
  have p0087 :=
    @g_a1i (syn_wbr C (syn_clec) C) (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) p0086
  have p0088 :=
    @g_iffalse (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C
  have p0089 :=
    @g_breq1d (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) C C (syn_clec) p0088
  have p0090 :=
    @g_mpbird (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wbr C (syn_clec) C) p0087 p0089
  have p0091 :=
    @g_pm2_61i (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) p0081 p0090
  have p0092 :=
    @g_tru
  have p0093 :=
    @g_simpr syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
  have p0094 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0095 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0093 p0094
  have p0096 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)))) hyp_wppreachtchwboundedndv_8
  have p0097 :=
    @g_ifclda syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C (syn_chwcards (syn_cvv)) p0095 p0096
  have p0098 :=
    Nominal.mp p0092 p0097
  have p0099 :=
    @g_pm3_2i (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs))))) p0098 hyp_wppreachtchwboundedndv_7
  have p0100 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
  have p0101 :=
    @g_breq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) C (syn_clec) p0100
  have p0102 :=
    @g_eqidd (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) F
  have p0103 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
  have p0104 :=
    @g_jca (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.classEq F F) (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) p0102 p0103
  have p0105 :=
    @g_freceq12 F F (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
  have p0106 :=
    @g_syl (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_wa (.classEq F F) (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))) (.classEq (syn_cfrec F (.cv p)) (syn_cfrec F (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))) p0104 p0105
  have p0107 :=
    @g_fveq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r) (syn_cfrec F (.cv p)) (syn_cfrec F (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) p0106
  have p0108 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cfv (syn_cfrec F (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r)) (syn_cncs) p0107
  have p0109 :=
    @g_ralbidv (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r)) (syn_cncs)) r (syn_cnnc) dv_cache_0004 p0108
  have p0110 :=
    @g_imbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs))) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r)) (syn_cncs))) p0101 p0109
  have p0111 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs)))) (.imp (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r)) (syn_cncs)))) p (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0005 p0110
  have p0112 :=
    Nominal.mp p0099 p0111
  have p0113 :=
    Nominal.mp p0091 p0112
  have p0114 :=
    @g_wppreachtcbidv x C (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) F G r dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 hyp_wppreachtchwboundedndv_1 p0039 hyp_wppreachtchwboundedndv_2 hyp_wppreachtchwboundedndv_3 p0074 hyp_wppreachtchwboundedndv_4 hyp_wppreachtchwboundedndv_5 p0077 p0113
  have p0115 :=
    @g_dedth (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wb (.classMem (.cv d) (syn_cwppreach F C)) (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C)))) (syn_wb (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cwppreach F C)) (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cwppreach G (syn_ctc C)))) (.cv d) C p0004 p0114
  exact p0115

#print axioms g_wppreachtchwboundedndv

end NFChoice.DirectNominalPrf.WPPReplay
