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
import NominalWPPReplayChunk012BCompact001Part004

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

noncomputable def g_isoini
    (A : Class) (B : Class) (D : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wiso H R S A B) (.classMem D A)) (.classEq (syn_cima H (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))) (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ H.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wiso H R S A B) (.classMem D A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_H, fresh_x_not_R, fresh_x_not_S, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wbr (.cv y) S (syn_cfv H D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_D, fresh_x_not_H, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_S, fresh_y_not_D, fresh_y_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_wa (syn_wiso H R S A B) (.classMem D A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_H, fresh_y_not_R, fresh_y_not_S, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_R, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have p0000 :=
    @g_elin (.cv y) B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))
  have p0001 :=
    @g_eliniseg S (syn_cfv H D) (.cv y)
  have p0002 :=
    @g_anbi2i (.classMem (.cv y) (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))) (syn_wbr (.cv y) S (syn_cfv H D)) (.classMem (.cv y) B) p0001
  have p0003 :=
    @g_bitri (.classMem (.cv y) (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D))))) (syn_wa (.classMem (.cv y) B) (.classMem (.cv y) (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D))))) (syn_wa (.classMem (.cv y) B) (syn_wbr (.cv y) S (syn_cfv H D))) p0000 p0002
  have p0004 :=
    @g_isof1o A B R S H
  have p0005 :=
    @g_f1ofo A B H
  have p0006 :=
    @g_syl (syn_wiso H R S A B) (syn_wf1o H A B) (syn_wfo H A B) p0004 p0005
  have p0007 :=
    @g_forn A B H
  have p0008 :=
    @g_syl (syn_wiso H R S A B) (syn_wfo H A B) (.classEq (syn_crn H) B) p0006 p0007
  have p0009 :=
    @g_eleq2d (syn_wiso H R S A B) (syn_crn H) B (.cv y) p0008
  have p0010 :=
    @g_f1ofn A B H
  have p0011 :=
    @g_syl (syn_wiso H R S A B) (syn_wf1o H A B) (syn_wfn H A) p0004 p0010
  have p0012 :=
    @g_fvelrnb x A (.cv y) H dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0013 :=
    @g_syl (syn_wiso H R S A B) (syn_wfn H A) (syn_wb (.classMem (.cv y) (syn_crn H)) (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y)))) p0011 p0012
  have p0014 :=
    @g_bitr3d (syn_wiso H R S A B) (.classMem (.cv y) (syn_crn H)) (.classMem (.cv y) B) (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y))) p0009 p0013
  have p0015 :=
    @g_anbi1d (syn_wiso H R S A B) (.classMem (.cv y) B) (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y))) (syn_wbr (.cv y) S (syn_cfv H D)) p0014
  have p0016 :=
    @g_adantr (syn_wiso H R S A B) (syn_wb (syn_wa (.classMem (.cv y) B) (syn_wbr (.cv y) S (syn_cfv H D))) (syn_wa (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y))) (syn_wbr (.cv y) S (syn_cfv H D)))) (.classMem D A) p0015
  have p0017 :=
    @g_elin (.cv x) A (syn_cima (syn_ccnv R) (syn_csn D))
  have p0018 :=
    @g_eliniseg R D (.cv x)
  have p0019 :=
    @g_anbi2i (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) R D) (.classMem (.cv x) A) p0018
  have p0020 :=
    @g_bitri (.classMem (.cv x) (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) (syn_cima (syn_ccnv R) (syn_csn D)))) (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) R D)) p0017 p0019
  have p0021 :=
    @g_anbi1i (.classMem (.cv x) (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))) (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) R D)) (syn_wbr (.cv x) H (.cv y)) p0020
  have p0022 :=
    @g_anass (.classMem (.cv x) A) (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y))
  have p0023 :=
    @g_bitri (syn_wa (.classMem (.cv x) (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))) (syn_wbr (.cv x) H (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) R D)) (syn_wbr (.cv x) H (.cv y))) (syn_wa (.classMem (.cv x) A) (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y)))) p0021 p0022
  have p0024 :=
    @g_fnbrfvb A (.cv x) (.cv y) H
  have p0025 :=
    @g_sylan (syn_wiso H R S A B) (syn_wfn H A) (.classMem (.cv x) A) (syn_wb (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv x) H (.cv y))) p0011 p0024
  have p0026 :=
    @g_adantrr (syn_wiso H R S A B) (.classMem (.cv x) A) (syn_wb (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv x) H (.cv y))) (.classMem D A) p0025
  have p0027 :=
    @g_bicomd (syn_wa (syn_wiso H R S A B) (syn_wa (.classMem (.cv x) A) (.classMem D A))) (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv x) H (.cv y)) p0026
  have p0028 :=
    @g_isorel A B (.cv x) D R S H
  have p0029 :=
    @g_anbi12d (syn_wa (syn_wiso H R S A B) (syn_wa (.classMem (.cv x) A) (.classMem D A))) (syn_wbr (.cv x) H (.cv y)) (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv x) R D) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H D)) p0027 p0028
  have p0030 :=
    @g_ancom (syn_wbr (.cv x) H (.cv y)) (syn_wbr (.cv x) R D)
  have p0031 :=
    @g_breq1 (syn_cfv H (.cv x)) (.cv y) (syn_cfv H D) S
  have p0032 :=
    @g_pm5_32i (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H D)) (syn_wbr (.cv y) S (syn_cfv H D)) p0031
  have p0033 :=
    @g_n_3bitr3g (syn_wa (syn_wiso H R S A B) (syn_wa (.classMem (.cv x) A) (.classMem D A))) (syn_wa (syn_wbr (.cv x) H (.cv y)) (syn_wbr (.cv x) R D)) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H D))) (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y))) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D))) p0029 p0030 p0032
  have p0034 :=
    @g_exp32 (syn_wiso H R S A B) (.classMem (.cv x) A) (.classMem D A) (syn_wb (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y))) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D)))) p0033
  have p0035 :=
    @g_com23 (syn_wiso H R S A B) (.classMem (.cv x) A) (.classMem D A) (syn_wb (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y))) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D)))) p0034
  have p0036 :=
    @g_imp (syn_wiso H R S A B) (.classMem D A) (.imp (.classMem (.cv x) A) (syn_wb (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y))) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D))))) p0035
  have p0037 :=
    @g_pm5_32d (syn_wa (syn_wiso H R S A B) (.classMem D A)) (.classMem (.cv x) A) (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y))) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D))) p0036
  have p0038 :=
    @g_syl5bb (syn_wa (.classMem (.cv x) (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))) (syn_wbr (.cv x) H (.cv y))) (syn_wa (.classMem (.cv x) A) (syn_wa (syn_wbr (.cv x) R D) (syn_wbr (.cv x) H (.cv y)))) (syn_wa (syn_wiso H R S A B) (.classMem D A)) (syn_wa (.classMem (.cv x) A) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D)))) p0023 p0037
  have p0039 :=
    @g_rexbidv2 (syn_wa (syn_wiso H R S A B) (.classMem D A)) (syn_wbr (.cv x) H (.cv y)) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D))) x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) A dv_cache_0004 p0038
  have p0040 :=
    @g_r19_41v (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D)) x A dv_cache_0005
  have p0041 :=
    @g_syl6bb (syn_wa (syn_wiso H R S A B) (.classMem D A)) (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) H (.cv y))) (syn_wrex x A (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv y)) (syn_wbr (.cv y) S (syn_cfv H D)))) (syn_wa (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y))) (syn_wbr (.cv y) S (syn_cfv H D))) p0039 p0040
  have p0042 :=
    @g_bitr4d (syn_wa (syn_wiso H R S A B) (.classMem D A)) (syn_wa (.classMem (.cv y) B) (syn_wbr (.cv y) S (syn_cfv H D))) (syn_wa (syn_wrex x A (.classEq (syn_cfv H (.cv x)) (.cv y))) (syn_wbr (.cv y) S (syn_cfv H D))) (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) H (.cv y))) p0016 p0041
  have p0043 :=
    @g_syl5bb (.classMem (.cv y) (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D))))) (syn_wa (.classMem (.cv y) B) (syn_wbr (.cv y) S (syn_cfv H D))) (syn_wa (syn_wiso H R S A B) (.classMem D A)) (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) H (.cv y))) p0003 p0042
  have p0044 :=
    @g_eqabdv (syn_wa (syn_wiso H R S A B) (.classMem D A)) (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) H (.cv y))) y (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))) dv_cache_0006 dv_cache_0007 p0043
  have p0045 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x H (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) dv_cache_0008 dv_cache_0003 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0046 :=
    @g_syl6reqr (syn_wa (syn_wiso H R S A B) (.classMem D A)) (syn_cin B (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H D)))) (.cab y (syn_wrex x (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D))) (syn_wbr (.cv x) H (.cv y)))) (syn_cima H (syn_cin A (syn_cima (syn_ccnv R) (syn_csn D)))) p0044 p0045
  exact p0046

#print axioms g_isoini

end NFChoice.DirectNominalPrf.WPPReplay
