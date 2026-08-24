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
import NominalWPPReplayChunk012BCompact001Part002

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

noncomputable def g_isores2
    (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf (syn_wb (syn_wiso H R S A B) (syn_wiso H R (syn_cin S (syn_cxp B B)) A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ H.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
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
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
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
  have dv_cache_0001 : y ∉ ((syn_wa (syn_wf1o H A B) (.classMem (.cv x) A))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_H, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wf1o H A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0014 : x ∉ ((syn_cin S (syn_cxp B B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cin S (syn_cxp B B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_S, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_f1of A B H
  have p0001 :=
    @g_ffvelrn A B (.cv x) H
  have p0002 :=
    @g_adantrr (syn_wf H A B) (.classMem (.cv x) A) (.classMem (syn_cfv H (.cv x)) B) (.classMem (.cv y) A) p0001
  have p0003 :=
    @g_ffvelrn A B (.cv y) H
  have p0004 :=
    @g_adantrl (syn_wf H A B) (.classMem (.cv y) A) (.classMem (syn_cfv H (.cv y)) B) (.classMem (.cv x) A) p0003
  have p0005 :=
    @g_brinxp (syn_cfv H (.cv x)) (syn_cfv H (.cv y)) B B S
  have p0006 :=
    @g_syl2anc (syn_wa (syn_wf H A B) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))) (.classMem (syn_cfv H (.cv x)) B) (.classMem (syn_cfv H (.cv y)) B) (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y)))) p0002 p0004 p0005
  have p0007 :=
    @g_sylan (syn_wf1o H A B) (syn_wf H A B) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y)))) p0000 p0006
  have p0008 :=
    @g_anassrs (syn_wf1o H A B) (.classMem (.cv x) A) (.classMem (.cv y) A) (syn_wb (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y)))) p0007
  have p0009 :=
    @g_bibi2d (syn_wa (syn_wa (syn_wf1o H A B) (.classMem (.cv x) A)) (.classMem (.cv y) A)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y))) (syn_wbr (.cv x) R (.cv y)) p0008
  have p0010 :=
    @g_ralbidva (syn_wa (syn_wf1o H A B) (.classMem (.cv x) A)) (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))) (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y)))) y A dv_cache_0001 p0009
  have p0011 :=
    @g_ralbidva (syn_wf1o H A B) (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))) (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y))))) x A dv_cache_0002 p0010
  have p0012 :=
    @g_pm5_32i (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y)))))) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y)))))) p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R S H dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0014 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso x y A B R (syn_cin S (syn_cxp B B)) H dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0014 dv_cache_0015 dv_cache_0013
  have p0015 :=
    @g_n_3bitr4i (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) S (syn_cfv H (.cv y))))))) (syn_wa (syn_wf1o H A B) (syn_wral x A (syn_wral y A (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (syn_cfv H (.cv x)) (syn_cin S (syn_cxp B B)) (syn_cfv H (.cv y))))))) (syn_wiso H R S A B) (syn_wiso H R (syn_cin S (syn_cxp B B)) A B) p0012 p0013 p0014
  exact p0015

noncomputable def g_isores1
    (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) :
    Nominal.NPrf (syn_wb (syn_wiso H R S A B) (syn_wiso H (syn_cin R (syn_cxp A A)) S A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ H.fv
  have p0000 :=
    @g_isocnv A B R S H
  have p0001 :=
    @g_isores2 B A S R (syn_ccnv H)
  have p0002 :=
    @g_sylib (syn_wiso H R S A B) (syn_wiso (syn_ccnv H) S R B A) (syn_wiso (syn_ccnv H) S (syn_cin R (syn_cxp A A)) B A) p0000 p0001
  have p0003 :=
    @g_isocnv B A S (syn_cin R (syn_cxp A A)) (syn_ccnv H)
  have p0004 :=
    @g_syl (syn_wiso H R S A B) (syn_wiso (syn_ccnv H) S (syn_cin R (syn_cxp A A)) B A) (syn_wiso (syn_ccnv (syn_ccnv H)) (syn_cin R (syn_cxp A A)) S A B) p0002 p0003
  have p0005 :=
    @g_cnvcnv H
  have p0006 :=
    @g_isoeq1 A B (syn_cin R (syn_cxp A A)) S H (syn_ccnv (syn_ccnv H))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_sylib (syn_wiso H R S A B) (syn_wiso (syn_ccnv (syn_ccnv H)) (syn_cin R (syn_cxp A A)) S A B) (syn_wiso H (syn_cin R (syn_cxp A A)) S A B) p0004 p0007
  have p0009 :=
    @g_isocnv A B (syn_cin R (syn_cxp A A)) S H
  have p0010 :=
    @g_sylibr (syn_wiso H (syn_cin R (syn_cxp A A)) S A B) (syn_wiso (syn_ccnv H) S (syn_cin R (syn_cxp A A)) B A) (syn_wiso (syn_ccnv H) S R B A) p0009 p0001
  have p0011 :=
    @g_isocnv B A S R (syn_ccnv H)
  have p0012 :=
    @g_syl (syn_wiso H (syn_cin R (syn_cxp A A)) S A B) (syn_wiso (syn_ccnv H) S R B A) (syn_wiso (syn_ccnv (syn_ccnv H)) R S A B) p0010 p0011
  have p0013 :=
    @g_isoeq1 A B R S H (syn_ccnv (syn_ccnv H))
  have p0014 :=
    Nominal.mp p0005 p0013
  have p0015 :=
    @g_sylib (syn_wiso H (syn_cin R (syn_cxp A A)) S A B) (syn_wiso (syn_ccnv (syn_ccnv H)) R S A B) (syn_wiso H R S A B) p0012 p0014
  have p0016 :=
    @g_impbii (syn_wiso H R S A B) (syn_wiso H (syn_cin R (syn_cxp A A)) S A B) p0008 p0015
  exact p0016

#print axioms g_isores1

end NFChoice.DirectNominalPrf.WPPReplay
