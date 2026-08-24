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
import NominalWPPReplayChunk013Compact001Part030

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

noncomputable def g_mapvalg
    (A : Class) (B : Class) (C : Class) (D : Class) (f : Var) (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.classMem B D)) (.classEq (syn_co A (syn_cmap) B) (.cab f (syn_wf (.cv f) B A)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ ({f} : Finset Var)
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : f ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.classEq (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((Wff.classEq (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_y, dv_B_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0006 : f ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((Class.cab f (syn_wf (.cv f) (.cv y) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_A, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Class.cab f (syn_wf (.cv f) B A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_A, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cab f (syn_wf (.cv f) B A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_A, fresh_y_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_mapex B A D C f dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_ancoms (.classMem B D) (.classMem A C) (.classMem (.cab f (syn_wf (.cv f) B A)) (syn_cvv)) p0000
  have p0002 :=
    @g_elex A C
  have p0003 :=
    @g_elex B D
  have p0004 :=
    @g_feq3 (.cv x) A (.cv y) (.cv f)
  have p0005 :=
    @g_abbidv (.classEq (.cv x) A) (syn_wf (.cv f) (.cv y) (.cv x)) (syn_wf (.cv f) (.cv y) A) f dv_cache_0003 p0004
  have p0006 :=
    @g_feq2 (.cv y) B A (.cv f)
  have p0007 :=
    @g_abbidv (.classEq (.cv y) B) (syn_wf (.cv f) (.cv y) A) (syn_wf (.cv f) B A) f dv_cache_0004 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_map x y f dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0009 :=
    @g_ovmpt2g x y A B (syn_cvv) (syn_cvv) (.cab f (syn_wf (.cv f) (.cv y) (.cv x))) (.cab f (syn_wf (.cv f) B A)) (syn_cmap) (.cab f (syn_wf (.cv f) (.cv y) A)) (syn_cvv) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0007 p0005 p0007 p0008
  have p0010 :=
    @g_n_3expia (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (.cab f (syn_wf (.cv f) B A)) (syn_cvv)) (.classEq (syn_co A (syn_cmap) B) (.cab f (syn_wf (.cv f) B A))) p0009
  have p0011 :=
    @g_syl2an (.classMem A C) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.imp (.classMem (.cab f (syn_wf (.cv f) B A)) (syn_cvv)) (.classEq (syn_co A (syn_cmap) B) (.cab f (syn_wf (.cv f) B A)))) (.classMem B D) p0002 p0003 p0010
  have p0012 :=
    @g_mpd (syn_wa (.classMem A C) (.classMem B D)) (.classMem (.cab f (syn_wf (.cv f) B A)) (syn_cvv)) (.classEq (syn_co A (syn_cmap) B) (.cab f (syn_wf (.cv f) B A))) p0001 p0011
  exact p0012

noncomputable def g_elmapg
    (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (X : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) (syn_wb (.classMem C (syn_co A (syn_cmap) B)) (syn_wf C B A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv ∪ X.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_g_not_V : g ∉ V.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_W : g ∉ W.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_X : g ∉ X.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have dv_cache_0001 : g ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : g ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((syn_wf C B A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_B, fresh_g_not_A, fresh_g_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_mapvalg A B V W g dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_eleq2d (syn_wa (.classMem A V) (.classMem B W)) (syn_co A (syn_cmap) B) (.cab g (syn_wf (.cv g) B A)) C p0000
  have p0002 :=
    @g_n_3adant3 (.classMem A V) (.classMem B W) (syn_wb (.classMem C (syn_co A (syn_cmap) B)) (.classMem C (.cab g (syn_wf (.cv g) B A)))) (.classMem C X) p0001
  have p0003 :=
    @g_feq1 B A (.cv g) C
  have p0004 :=
    @g_elabg (syn_wf (.cv g) B A) (syn_wf C B A) g C X dv_cache_0003 dv_cache_0004 p0003
  have p0005 :=
    @g_n_3ad2ant3 (.classMem C X) (.classMem A V) (syn_wb (.classMem C (.cab g (syn_wf (.cv g) B A))) (syn_wf C B A)) (.classMem B W) p0004
  have p0006 :=
    @g_bitrd (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) (.classMem C (syn_co A (syn_cmap) B)) (.classMem C (.cab g (syn_wf (.cv g) B A))) (syn_wf C B A) p0002 p0005
  exact p0006

noncomputable def g_elmapi
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_co B (syn_cmap) C)) (syn_wf A C B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_elovex1 A B C (syn_cmap)
  have p0001 :=
    @g_elovex2 A B C (syn_cmap)
  have p0002 :=
    @g_id (.classMem A (syn_co B (syn_cmap) C))
  have p0003 :=
    @g_elmapg B C A (syn_cvv) (syn_cvv) (syn_co B (syn_cmap) C)
  have p0004 :=
    @g_syl3anc (.classMem A (syn_co B (syn_cmap) C)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) (.classMem A (syn_co B (syn_cmap) C)) (syn_wb (.classMem A (syn_co B (syn_cmap) C)) (syn_wf A C B)) p0000 p0001 p0002 p0003
  have p0005 :=
    @g_ibi (.classMem A (syn_co B (syn_cmap) C)) (syn_wf A C B) p0004
  exact p0005

noncomputable def g_bren
    (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({f} : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : f ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, dv_B_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Wff.classEq (.cv x) A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.classEq (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_y, dv_B_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0005 : f ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_wex f (syn_wf1o (.cv f) A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_wex f (syn_wf1o (.cv f) A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex A B (syn_cen)
  have p0001 :=
    @g_vex f
  have p0002 :=
    @g_dmex (.cv f) p0001
  have p0003 :=
    @g_rnex (.cv f) p0001
  have p0004 :=
    @g_pm3_2i (.classMem (syn_cdm (.cv f)) (syn_cvv)) (.classMem (syn_crn (.cv f)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_f1odm A B (.cv f)
  have p0006 :=
    @g_eleq1d (syn_wf1o (.cv f) A B) (syn_cdm (.cv f)) A (syn_cvv) p0005
  have p0007 :=
    @g_f1ofo A B (.cv f)
  have p0008 :=
    @g_forn A B (.cv f)
  have p0009 :=
    @g_syl (syn_wf1o (.cv f) A B) (syn_wfo (.cv f) A B) (.classEq (syn_crn (.cv f)) B) p0007 p0008
  have p0010 :=
    @g_eleq1d (syn_wf1o (.cv f) A B) (syn_crn (.cv f)) B (syn_cvv) p0009
  have p0011 :=
    @g_anbi12d (syn_wf1o (.cv f) A B) (.classMem (syn_cdm (.cv f)) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem (syn_crn (.cv f)) (syn_cvv)) (.classMem B (syn_cvv)) p0006 p0010
  have p0012 :=
    @g_mpbii (syn_wf1o (.cv f) A B) (syn_wa (.classMem (syn_cdm (.cv f)) (syn_cvv)) (.classMem (syn_crn (.cv f)) (syn_cvv))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0004 p0011
  have p0013 :=
    @g_exlimiv (syn_wf1o (.cv f) A B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) f dv_cache_0001 p0012
  have p0014 :=
    @g_f1oeq2 (.cv x) A (.cv y) (.cv f)
  have p0015 :=
    @g_exbidv (.classEq (.cv x) A) (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wf1o (.cv f) A (.cv y)) f dv_cache_0002 p0014
  have p0016 :=
    @g_f1oeq3 (.cv y) B A (.cv f)
  have p0017 :=
    @g_exbidv (.classEq (.cv y) B) (syn_wf1o (.cv f) A (.cv y)) (syn_wf1o (.cv f) A B) f dv_cache_0003 p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_en x y f dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0019 :=
    @g_brabg (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y))) (syn_wex f (syn_wf1o (.cv f) A (.cv y))) (syn_wex f (syn_wf1o (.cv f) A B)) x y A B (syn_cvv) (syn_cvv) (syn_cen) dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0006 p0015 p0017 p0018
  have p0020 :=
    @g_pm5_21nii (syn_wbr A (syn_cen) B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wex f (syn_wf1o (.cv f) A B)) p0000 p0013 p0019
  exact p0020

noncomputable def g_enex
     :
    Nominal.NPrf (.classMem (syn_cen) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let f : Var := freshVar proofSupport 2
  let g : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_f : x ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_ne_g : x ≠ g := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_g_ne_x : g ≠ x :=
    Ne.symm fresh_x_ne_g
  have fresh_y_ne_f : y ≠ f := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_g_ne_y : g ≠ y :=
    Ne.symm fresh_y_ne_g
  have fresh_f_ne_g : f ≠ g := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_g_ne_f : g ≠ f :=
    Ne.symm fresh_f_ne_g
  have dv_cache_0001 : f ≠ x := by
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0002 : f ≠ y := by
    clear dv_cache_0001
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : f ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : g ∉ ((syn_cop (.cv f) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : g ∉ ((syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : g ∉ ((syn_ccnv (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : g ∉ ((syn_wfn (syn_ccnv (.cv f)) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_crn (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_crn (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_en x y f dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_elrn2 f (syn_cop (.cv x) (.cv y)) (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))) dv_cache_0004 dv_cache_0005
  have p0002 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cfns) (.cv x))))
  have p0003 :=
    @g_vex f
  have p0004 :=
    @g_brfns (.cv x) (.cv f) p0003
  have p0005 :=
    @g_bitr3i (.classMem (syn_cop (.cv f) (.cv x)) (syn_cfns)) (syn_wbr (.cv f) (syn_cfns) (.cv x)) (syn_wfn (.cv f) (.cv x)) p0002 p0004
  have p0006 :=
    @g_elrn2 g (syn_cop (.cv f) (.cv y)) (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)) dv_cache_0006 dv_cache_0007
  have p0007 :=
    @g_oteltxp (.cv g) (.cv f) (.cv y) (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)
  have p0008 :=
    @g_opelcnv (.cv g) (.cv f) (syn_cimage (syn_cswap))
  have p0009 :=
    @g_dfcnv2 (.cv f)
  have p0010 :=
    @g_eqeq2i (syn_ccnv (.cv f)) (syn_cima (syn_cswap) (.cv f)) (.cv g) p0009
  have p0011 :=
    @g_vex g
  have p0012 :=
    @g_brimage (.cv f) (.cv g) (syn_cswap) p0003 p0011
  have p0013 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (.cv g))))
  have p0014 :=
    @g_n_3bitr2ri (.classEq (.cv g) (syn_ccnv (.cv f))) (.classEq (.cv g) (syn_cima (syn_cswap) (.cv f))) (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (.cv g)) (.classMem (syn_cop (.cv f) (.cv g)) (syn_cimage (syn_cswap))) p0010 p0012 p0013
  have p0015 :=
    @g_bitri (.classMem (syn_cop (.cv g) (.cv f)) (syn_ccnv (syn_cimage (syn_cswap)))) (.classMem (syn_cop (.cv f) (.cv g)) (syn_cimage (syn_cswap))) (.classEq (.cv g) (syn_ccnv (.cv f))) p0008 p0014
  have p0016 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv g) (syn_cfns) (.cv y))))
  have p0017 :=
    @g_brfns (.cv y) (.cv g) p0011
  have p0018 :=
    @g_bitr3i (.classMem (syn_cop (.cv g) (.cv y)) (syn_cfns)) (syn_wbr (.cv g) (syn_cfns) (.cv y)) (syn_wfn (.cv g) (.cv y)) p0016 p0017
  have p0019 :=
    @g_anbi12i (.classMem (syn_cop (.cv g) (.cv f)) (syn_ccnv (syn_cimage (syn_cswap)))) (.classEq (.cv g) (syn_ccnv (.cv f))) (.classMem (syn_cop (.cv g) (.cv y)) (syn_cfns)) (syn_wfn (.cv g) (.cv y)) p0015 p0018
  have p0020 :=
    @g_bitri (.classMem (syn_cop (.cv g) (syn_cop (.cv f) (.cv y))) (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))) (syn_wa (.classMem (syn_cop (.cv g) (.cv f)) (syn_ccnv (syn_cimage (syn_cswap)))) (.classMem (syn_cop (.cv g) (.cv y)) (syn_cfns))) (syn_wa (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfn (.cv g) (.cv y))) p0007 p0019
  have p0021 :=
    @g_exbii (.classMem (syn_cop (.cv g) (syn_cop (.cv f) (.cv y))) (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))) (syn_wa (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfn (.cv g) (.cv y))) g p0020
  have p0022 :=
    @g_cnvex (.cv f) p0003
  have p0023 :=
    @g_fneq1 (.cv y) (.cv g) (syn_ccnv (.cv f))
  have p0024 :=
    @g_ceqsexv (syn_wfn (.cv g) (.cv y)) (syn_wfn (syn_ccnv (.cv f)) (.cv y)) g (syn_ccnv (.cv f)) dv_cache_0008 dv_cache_0009 p0022 p0023
  have p0025 :=
    @g_bitri (syn_wex g (.classMem (syn_cop (.cv g) (syn_cop (.cv f) (.cv y))) (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))) (syn_wex g (syn_wa (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfn (.cv g) (.cv y)))) (syn_wfn (syn_ccnv (.cv f)) (.cv y)) p0021 p0024
  have p0026 :=
    @g_bitri (.classMem (syn_cop (.cv f) (.cv y)) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))) (syn_wex g (.classMem (syn_cop (.cv g) (syn_cop (.cv f) (.cv y))) (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))) (syn_wfn (syn_ccnv (.cv f)) (.cv y)) p0006 p0025
  have p0027 :=
    @g_anbi12i (.classMem (syn_cop (.cv f) (.cv x)) (syn_cfns)) (syn_wfn (.cv f) (.cv x)) (.classMem (syn_cop (.cv f) (.cv y)) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))) (syn_wfn (syn_ccnv (.cv f)) (.cv y)) p0005 p0026
  have p0028 :=
    @g_oteltxp (.cv f) (.cv x) (.cv y) (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))
  have p0029 :=
    @g_dff1o4 (.cv x) (.cv y) (.cv f)
  have p0030 :=
    @g_n_3bitr4i (syn_wa (.classMem (syn_cop (.cv f) (.cv x)) (syn_cfns)) (.classMem (syn_cop (.cv f) (.cv y)) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))) (syn_wa (syn_wfn (.cv f) (.cv x)) (syn_wfn (syn_ccnv (.cv f)) (.cv y))) (.classMem (syn_cop (.cv f) (syn_cop (.cv x) (.cv y))) (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))) (syn_wf1o (.cv f) (.cv x) (.cv y)) p0027 p0028 p0029
  have p0031 :=
    @g_exbii (.classMem (syn_cop (.cv f) (syn_cop (.cv x) (.cv y))) (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))) (syn_wf1o (.cv f) (.cv x) (.cv y)) f p0030
  have p0032 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_crn (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))) (syn_wex f (.classMem (syn_cop (.cv f) (syn_cop (.cv x) (.cv y))) (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))) (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y))) p0001 p0031
  have p0033 :=
    @g_opabbi2i (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y))) x y (syn_crn (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))) dv_cache_0010 dv_cache_0011 dv_cache_0003 p0032
  have p0034 :=
    @g_eqtr4i (syn_cen) (syn_copab x y (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y)))) (syn_crn (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))) p0000 p0033
  have p0035 :=
    @g_fnsex
  have p0036 :=
    @g_swapex
  have p0037 :=
    @g_imageex (syn_cswap) p0036
  have p0038 :=
    @g_cnvex (syn_cimage (syn_cswap)) p0037
  have p0039 :=
    @g_fnsex
  have p0040 :=
    @g_txpex (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns) p0038 p0039
  have p0041 :=
    @g_rnex (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)) p0040
  have p0042 :=
    @g_txpex (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))) p0035 p0041
  have p0043 :=
    @g_rnex (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))) p0042
  have p0044 :=
    @g_eqeltri (syn_cen) (syn_crn (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))) (syn_cvv) p0034 p0043
  exact p0044

noncomputable def g_f1oeng
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem F C) (syn_wf1o F A B)) (syn_wbr A (syn_cen) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let f : Var := freshVar proofSupport 0
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
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((syn_wf1o F A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, fresh_f_not_B, fresh_f_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_f1oeq1 A B (.cv f) F
  have p0001 :=
    @g_spcegv (syn_wf1o (.cv f) A B) (syn_wf1o F A B) f F C dv_cache_0001 dv_cache_0002 p0000
  have p0002 :=
    @g_imp (.classMem F C) (syn_wf1o F A B) (syn_wex f (syn_wf1o (.cv f) A B)) p0001
  have p0003 :=
    @g_bren A B f dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_sylibr (syn_wa (.classMem F C) (syn_wf1o F A B)) (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wbr A (syn_cen) B) p0002 p0003
  exact p0004

noncomputable def g_f1oen
    (A : Class) (B : Class) (F : Class) (hyp_f1oen_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wbr A (syn_cen) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_f1oeng A B (syn_cvv) F
  have p0001 :=
    @g_mpan (.classMem F (syn_cvv)) (syn_wf1o F A B) (syn_wbr A (syn_cen) B) hyp_f1oen_1 p0000
  exact p0001

noncomputable def g_enrflxg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wbr A (syn_cen) A)) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_idex
  have p0001 :=
    @g_resexg (syn_cid) A (syn_cvv) V
  have p0002 :=
    @g_mpan (.classMem (syn_cid) (syn_cvv)) (.classMem A V) (.classMem (syn_cres (syn_cid) A) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_f1oi A
  have p0004 :=
    @g_f1oeng A A (syn_cvv) (syn_cres (syn_cid) A)
  have p0005 :=
    @g_sylancl (.classMem A V) (.classMem (syn_cres (syn_cid) A) (syn_cvv)) (syn_wf1o (syn_cres (syn_cid) A) A A) (syn_wbr A (syn_cen) A) p0002 p0003 p0004
  exact p0005

noncomputable def g_enrflx
    (A : Class) (hyp_enrflx_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr A (syn_cen) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_enrflxg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_enrflx_1 p0000
  exact p0001

noncomputable def g_ensymi
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
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
  have dv_cache_0003 : f ∉ ((syn_wbr B (syn_cen) A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_bren A B f dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_f1ocnv A B (.cv f)
  have p0002 :=
    @g_vex f
  have p0003 :=
    @g_cnvex (.cv f) p0002
  have p0004 :=
    @g_f1oen B A (syn_ccnv (.cv f)) p0003
  have p0005 :=
    @g_syl (syn_wf1o (.cv f) A B) (syn_wf1o (syn_ccnv (.cv f)) B A) (syn_wbr B (syn_cen) A) p0001 p0004
  have p0006 :=
    @g_exlimiv (syn_wf1o (.cv f) A B) (syn_wbr B (syn_cen) A) f dv_cache_0003 p0005
  have p0007 :=
    @g_sylbi (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wbr B (syn_cen) A) p0000 p0006
  exact p0007

noncomputable def g_ensym
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_ensymi A B
  have p0001 :=
    @g_ensymi B A
  have p0002 :=
    @g_impbii (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) A) p0000 p0001
  exact p0002

noncomputable def g_entr
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) C)) (syn_wbr A (syn_cen) C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let f : Var := freshVar proofSupport 0
  let g : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_C : g ∉ C.fv := by
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
  have dv_cache_0003 : g ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : g ∉ ((syn_wf1o (.cv f) A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, fresh_g_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : f ∉ ((syn_wf1o (.cv g) B C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, fresh_f_not_C, fresh_f_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : f ∉ ((syn_wbr A (syn_cen) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, fresh_f_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : g ∉ ((syn_wbr A (syn_cen) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_bren A B f dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_bren B C g dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_anbi12i (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wbr B (syn_cen) C) (syn_wex g (syn_wf1o (.cv g) B C)) p0000 p0001
  have p0003 :=
    @g_eeanv (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C) f g dv_cache_0005 dv_cache_0006
  have p0004 :=
    @g_bitr4i (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) C)) (syn_wa (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wex g (syn_wf1o (.cv g) B C))) (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C)))) p0002 p0003
  have p0005 :=
    @g_f1oco A B C (.cv g) (.cv f)
  have p0006 :=
    @g_ancoms (syn_wf1o (.cv g) B C) (syn_wf1o (.cv f) A B) (syn_wf1o (syn_ccom (.cv g) (.cv f)) A C) p0005
  have p0007 :=
    @g_vex g
  have p0008 :=
    @g_vex f
  have p0009 :=
    @g_coex (.cv g) (.cv f) p0007 p0008
  have p0010 :=
    @g_f1oen A C (syn_ccom (.cv g) (.cv f)) p0009
  have p0011 :=
    @g_syl (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C)) (syn_wf1o (syn_ccom (.cv g) (.cv f)) A C) (syn_wbr A (syn_cen) C) p0006 p0010
  have p0012 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C)) (syn_wbr A (syn_cen) C) f g dv_cache_0007 dv_cache_0008 p0011
  have p0013 :=
    @g_sylbi (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) C)) (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C)))) (syn_wbr A (syn_cen) C) p0004 p0012
  exact p0013

#print axioms g_entr

end NFChoice.DirectNominalPrf.WPPReplay
