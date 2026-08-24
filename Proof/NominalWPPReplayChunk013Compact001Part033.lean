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
import NominalWPPReplayChunk013Compact001Part032

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

noncomputable def g_unen
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D)) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))) (syn_wbr (syn_cun A C) (syn_cen) (syn_cun B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let f : Var := freshVar proofSupport 0
  let g : Var := freshVar proofSupport 1
  let h : Var := freshVar proofSupport 2
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_D : g ∉ D.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_h_not_B : h ∉ B.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_C : h ∉ C.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_f_ne_g : f ≠ g := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_g_ne_f : g ≠ f :=
    Ne.symm fresh_f_ne_g
  have fresh_f_ne_h : f ≠ h := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_h_ne_f : h ≠ f :=
    Ne.symm fresh_f_ne_h
  have fresh_g_ne_h : g ≠ h := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_h_ne_g : h ≠ g :=
    Ne.symm fresh_g_ne_h
  have dv_cache_0001 : h ∉ ((syn_cun (.cv f) (.cv g))).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_f, fresh_h_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((syn_wf1o (syn_cun (.cv f) (.cv g)) (syn_cun A C) (syn_cun B D))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, fresh_h_not_C, fresh_h_not_B, fresh_h_not_D, fresh_h_ne_f, fresh_h_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, fresh_f_not_C, fresh_f_not_B, fresh_f_not_D, fresh_f_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((Wff.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_C, fresh_g_not_B, fresh_g_not_D, fresh_g_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : f ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : g ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : g ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : g ∉ ((syn_wf1o (.cv f) A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, fresh_g_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : f ∉ ((syn_wf1o (.cv g) C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_C, fresh_f_not_D, fresh_f_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : h ∉ ((syn_cun A C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_A, fresh_h_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : h ∉ ((syn_cun B D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_not_B, fresh_h_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_f1oun A B C D (.cv f) (.cv g)
  have p0001 :=
    @g_vex f
  have p0002 :=
    @g_vex g
  have p0003 :=
    @g_unex (.cv f) (.cv g) p0001 p0002
  have p0004 :=
    @g_f1oeq1 (syn_cun A C) (syn_cun B D) (.cv h) (syn_cun (.cv f) (.cv g))
  have p0005 :=
    @g_spcev (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D)) (syn_wf1o (syn_cun (.cv f) (.cv g)) (syn_cun A C) (syn_cun B D)) h (syn_cun (.cv f) (.cv g)) dv_cache_0001 dv_cache_0002 p0003 p0004
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))) (syn_wf1o (syn_cun (.cv f) (.cv g)) (syn_cun A C) (syn_cun B D)) (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))) p0000 p0005
  have p0007 :=
    @g_ex (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))) p0006
  have p0008 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)) (.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D)))) f g dv_cache_0003 dv_cache_0004 p0007
  have p0009 :=
    @g_imp (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)))) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))) p0008
  have p0010 :=
    @g_bren A B f dv_cache_0005 dv_cache_0006
  have p0011 :=
    @g_bren C D g dv_cache_0007 dv_cache_0008
  have p0012 :=
    @g_anbi12i (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wbr C (syn_cen) D) (syn_wex g (syn_wf1o (.cv g) C D)) p0010 p0011
  have p0013 :=
    @g_eeanv (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D) f g dv_cache_0009 dv_cache_0010
  have p0014 :=
    @g_bitr4i (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D)) (syn_wa (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wex g (syn_wf1o (.cv g) C D))) (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)))) p0012 p0013
  have p0015 :=
    @g_anbi1i (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D)) (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)))) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) p0014
  have p0016 :=
    @g_bren (syn_cun A C) (syn_cun B D) h dv_cache_0011 dv_cache_0012
  have p0017 :=
    @g_n_3imtr4i (syn_wa (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)))) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))) (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))) (syn_wa (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D)) (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))) (syn_wbr (syn_cun A C) (syn_cen) (syn_cun B D)) p0009 p0015 p0016
  exact p0017

noncomputable def g_xpsnen
    (A : Class) (B : Class) (hyp_xpsnen_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_xpsnen_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cxp A (syn_csn B)) (syn_cen) A) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_snid B hyp_xpsnen_2
  have p0001 :=
    @g_ne0i (syn_csn B) B
  have p0002 :=
    @g_dmxp A (syn_csn B)
  have p0003 :=
    @g_mp2b (.classMem B (syn_csn B)) (syn_wne (syn_csn B) (syn_c0)) (.classEq (syn_cdm (syn_cxp A (syn_csn B))) A) p0000 p0001 p0002
  have p0004 :=
    @g_fconst A B hyp_xpsnen_2
  have p0005 :=
    @g_ffun A (syn_csn B) (syn_cxp A (syn_csn B))
  have p0006 :=
    @g_snex B
  have p0007 :=
    @g_xpex A (syn_csn B) hyp_xpsnen_1 p0006
  have p0008 :=
    @g_fundmen (syn_cxp A (syn_csn B)) p0007
  have p0009 :=
    @g_mp2b (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B)) (syn_wfun (syn_cxp A (syn_csn B))) (syn_wbr (syn_cdm (syn_cxp A (syn_csn B))) (syn_cen) (syn_cxp A (syn_csn B))) p0004 p0005 p0008
  have p0010 :=
    @g_eqbrtrri (syn_cdm (syn_cxp A (syn_csn B))) A (syn_cxp A (syn_csn B)) (syn_cen) p0003 p0009
  have p0011 :=
    @g_ensym A (syn_cxp A (syn_csn B))
  have p0012 :=
    @g_mpbi (syn_wbr A (syn_cen) (syn_cxp A (syn_csn B))) (syn_wbr (syn_cxp A (syn_csn B)) (syn_cen) A) p0010 p0011
  exact p0012

noncomputable def g_xpcomen
    (A : Class) (B : Class) (hyp_xpcomen_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_xpcomen_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cxp A B) (syn_cen) (syn_cxp B A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_swapres (syn_cxp A B)
  have p0001 :=
    @g_cnvxp A B
  have p0002 :=
    @g_f1oeq3 (syn_ccnv (syn_cxp A B)) (syn_cxp B A) (syn_cxp A B) (syn_cres (syn_cswap) (syn_cxp A B))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_mpbi (syn_wf1o (syn_cres (syn_cswap) (syn_cxp A B)) (syn_cxp A B) (syn_ccnv (syn_cxp A B))) (syn_wf1o (syn_cres (syn_cswap) (syn_cxp A B)) (syn_cxp A B) (syn_cxp B A)) p0000 p0003
  have p0005 :=
    @g_swapex
  have p0006 :=
    @g_xpex A B hyp_xpcomen_1 hyp_xpcomen_2
  have p0007 :=
    @g_resex (syn_cswap) (syn_cxp A B) p0005 p0006
  have p0008 :=
    @g_f1oen (syn_cxp A B) (syn_cxp B A) (syn_cres (syn_cswap) (syn_cxp A B)) p0007
  have p0009 :=
    Nominal.mp p0004 p0008
  exact p0009

noncomputable def g_xpen
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D)) (syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let f : Var := freshVar proofSupport 0
  let g : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_D : g ∉ D.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_f_ne_g : f ≠ g := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_g_ne_f : g ≠ f :=
    Ne.symm fresh_f_ne_g
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : g ∉ ((syn_wf1o (.cv f) A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, fresh_g_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : f ∉ ((syn_wf1o (.cv g) C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_C, fresh_f_not_D, fresh_f_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : f ∉ ((syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, fresh_f_not_C, fresh_f_not_B, fresh_f_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : g ∉ ((syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_C, fresh_g_not_B, fresh_g_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_bren A B f dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_bren C D g dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_anbi12i (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wbr C (syn_cen) D) (syn_wex g (syn_wf1o (.cv g) C D)) p0000 p0001
  have p0003 :=
    @g_eeanv (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D) f g dv_cache_0005 dv_cache_0006
  have p0004 :=
    @g_bitr4i (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D)) (syn_wa (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wex g (syn_wf1o (.cv g) C D))) (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)))) p0002 p0003
  have p0005 :=
    @g_f1opprod A C B D (.cv f) (.cv g)
  have p0006 :=
    @g_vex f
  have p0007 :=
    @g_vex g
  have p0008 :=
    @g_pprodex (.cv f) (.cv g) p0006 p0007
  have p0009 :=
    @g_f1oen (syn_cxp A C) (syn_cxp B D) (syn_cpprod (.cv f) (.cv g)) p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)) (syn_wf1o (syn_cpprod (.cv f) (.cv g)) (syn_cxp A C) (syn_cxp B D)) (syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D)) p0005 p0009
  have p0011 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)) (syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D)) f g dv_cache_0007 dv_cache_0008 p0010
  have p0012 :=
    @g_sylbi (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D)) (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)))) (syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D)) p0004 p0011
  exact p0012

#print axioms g_xpen

end NFChoice.DirectNominalPrf.WPPReplay
