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
import NominalWPPReplayChunk014Compact001Part041

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

noncomputable def g_hwnisohwisocl
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v_ne_u : v ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have dv_cache_0001 : u ≠ v := by
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0002 : u ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((Wff.imp (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ∉ ((Wff.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_C, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0001 :=
    @g_simpr (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0002 :=
    @g_breq2 (.cv v) C B (syn_chwniso A)
  have p0003 :=
    @g_breq2 (.cv v) C B (syn_chwiso A)
  have p0004 :=
    @g_imbi12d (.classEq (.cv v) C) (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wbr B (syn_chwiso A) C) p0002 p0003
  have p0005 :=
    @g_imbi2d (.classEq (.cv v) C) (.imp (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v))) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C)) (.classMem B (syn_cvv)) p0004
  have p0006 :=
    @g_breq1 (.cv u) B (.cv v) (syn_chwniso A)
  have p0007 :=
    @g_breq1 (.cv u) B (.cv v) (syn_chwiso A)
  have p0008 :=
    @g_imbi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v)) p0006 p0007
  have p0009 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0010 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) p0009
  have p0011 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0010
  have p0012 :=
    @g_vtoclg (.imp (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (.imp (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v))) u B (syn_cvv) dv_cache_0002 dv_cache_0003 p0008 p0011
  have p0013 :=
    @g_vtoclg (.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v)))) (.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C))) v C (syn_cvv) dv_cache_0004 dv_cache_0005 p0005 p0012
  have p0014 :=
    @g_syl (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem C (syn_cvv)) (.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C))) p0001 p0013
  have p0015 :=
    @g_mpd (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C)) p0000 p0014
  exact p0015

noncomputable def g_hwisowitnesscl
    (A : Class) (B : Class) (C : Class) (h : Var) (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) (dv_C_h : h ∉ C.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ ({h} : Finset Var)
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_h : v ≠ h := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_v : h ≠ v :=
    Ne.symm fresh_v_ne_h
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_ne_h : u ≠ h := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_u : h ≠ u :=
    Ne.symm fresh_u_ne_h
  have fresh_v_ne_u : v ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have dv_cache_0001 : h ∉ ((Wff.classEq (.cv v) C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_v, dv_C_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((Wff.classEq (.cv u) B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_u, dv_B_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0005 : h ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0006 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((Wff.imp (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v, fresh_u_not_A, fresh_u_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : v ∉ ((Wff.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_C, fresh_v_not_A, fresh_v_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0001 :=
    @g_simpr (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0002 :=
    @g_breq2 (.cv v) C B (syn_chwiso A)
  have p0003 :=
    @g_fveq2 (.cv v) C (syn_c1st)
  have p0004 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (.cv h)
  have p0005 :=
    @g_syl (.classEq (.cv v) C) (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C)) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) p0003 p0004
  have p0006 :=
    @g_fveq2 (.cv v) C (syn_c2nd)
  have p0007 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (.cv h)
  have p0008 :=
    @g_syl (.classEq (.cv v) C) (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C)) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) p0006 p0007
  have p0009 :=
    @g_bitrd (.classEq (.cv v) C) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)) p0005 p0008
  have p0010 :=
    @g_exbidv (.classEq (.cv v) C) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)) h dv_cache_0001 p0009
  have p0011 :=
    @g_imbi12d (.classEq (.cv v) C) (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wbr B (syn_chwiso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) p0002 p0010
  have p0012 :=
    @g_imbi2d (.classEq (.cv v) C) (.imp (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))) (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))) (.classMem B (syn_cvv)) p0011
  have p0013 :=
    @g_breq1 (.cv u) B (.cv v) (syn_chwiso A)
  have p0014 :=
    @g_fveq2 (.cv u) B (syn_c1st)
  have p0015 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B) (.cv h)
  have p0016 :=
    @g_syl (.classEq (.cv u) B) (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B)) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0014 p0015
  have p0017 :=
    @g_fveq2 (.cv u) B (syn_c2nd)
  have p0018 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0019 :=
    @g_syl (.classEq (.cv u) B) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B)) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) p0017 p0018
  have p0020 :=
    @g_bitrd (.classEq (.cv u) B) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) p0016 p0019
  have p0021 :=
    @g_exbidv (.classEq (.cv u) B) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) h dv_cache_0002 p0020
  have p0022 :=
    @g_imbi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) p0013 p0021
  have p0023 :=
    @g_brhwisoany v u A h dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0024 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) p0023
  have p0025 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0024
  have p0026 :=
    @g_vtoclg (.imp (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (.imp (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))) u B (syn_cvv) dv_cache_0006 dv_cache_0007 p0022 p0025
  have p0027 :=
    @g_vtoclg (.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))) (.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))) v C (syn_cvv) dv_cache_0008 dv_cache_0009 p0012 p0026
  have p0028 :=
    @g_syl (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem C (syn_cvv)) (.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))) p0001 p0027
  have p0029 :=
    @g_mpd (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))) p0000 p0028
  exact p0029

noncomputable def g_opfvscl
    (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v_ne_u : v ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have dv_cache_0001 : u ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((Wff.imp (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0001 :=
    @g_simpr (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0002 :=
    @g_opeq2 (.cv v) C B
  have p0003 :=
    @g_fveq2d (.classEq (.cv v) C) (syn_cop B (.cv v)) (syn_cop B C) (syn_c1st) p0002
  have p0004 :=
    @g_eqid B
  have p0005 :=
    @g_a1i (.classEq B B) (.classEq (.cv v) C) p0004
  have p0006 :=
    @g_eqeq12d (.classEq (.cv v) C) (syn_cfv (syn_c1st) (syn_cop B (.cv v))) (syn_cfv (syn_c1st) (syn_cop B C)) B B p0003 p0005
  have p0007 :=
    @g_opeq2 (.cv v) C B
  have p0008 :=
    @g_fveq2d (.classEq (.cv v) C) (syn_cop B (.cv v)) (syn_cop B C) (syn_c2nd) p0007
  have p0009 :=
    @g_id (.classEq (.cv v) C)
  have p0010 :=
    @g_eqeq12d (.classEq (.cv v) C) (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (syn_cfv (syn_c2nd) (syn_cop B C)) (.cv v) C p0008 p0009
  have p0011 :=
    @g_anbi12d (.classEq (.cv v) C) (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B) (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v)) (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C) p0006 p0010
  have p0012 :=
    @g_imbi2d (.classEq (.cv v) C) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C)) (.classMem B (syn_cvv)) p0011
  have p0013 :=
    @g_opeq1 (.cv u) B (.cv v)
  have p0014 :=
    @g_fveq2d (.classEq (.cv u) B) (syn_cop (.cv u) (.cv v)) (syn_cop B (.cv v)) (syn_c1st) p0013
  have p0015 :=
    @g_id (.classEq (.cv u) B)
  have p0016 :=
    @g_eqeq12d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (syn_cop (.cv u) (.cv v))) (syn_cfv (syn_c1st) (syn_cop B (.cv v))) (.cv u) B p0014 p0015
  have p0017 :=
    @g_opeq1 (.cv u) B (.cv v)
  have p0018 :=
    @g_fveq2d (.classEq (.cv u) B) (syn_cop (.cv u) (.cv v)) (syn_cop B (.cv v)) (syn_c2nd) p0017
  have p0019 :=
    @g_eqid (.cv v)
  have p0020 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0019
  have p0021 :=
    @g_eqeq12d (.classEq (.cv u) B) (syn_cfv (syn_c2nd) (syn_cop (.cv u) (.cv v))) (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v) (.cv v) p0018 p0020
  have p0022 :=
    @g_anbi12d (.classEq (.cv u) B) (.classEq (syn_cfv (syn_c1st) (syn_cop (.cv u) (.cv v))) (.cv u)) (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv u) (.cv v))) (.cv v)) (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v)) p0016 p0021
  have p0023 :=
    @g_vex u
  have p0024 :=
    @g_vex v
  have p0025 :=
    @g_opfv1st (.cv u) (.cv v) p0023 p0024
  have p0026 :=
    @g_vex u
  have p0027 :=
    @g_vex v
  have p0028 :=
    @g_opfv2nd (.cv u) (.cv v) p0026 p0027
  have p0029 :=
    @g_pm3_2i (.classEq (syn_cfv (syn_c1st) (syn_cop (.cv u) (.cv v))) (.cv u)) (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv u) (.cv v))) (.cv v)) p0025 p0028
  have p0030 :=
    @g_vtoclg (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (.cv u) (.cv v))) (.cv u)) (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv u) (.cv v))) (.cv v))) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v))) u B (syn_cvv) dv_cache_0001 dv_cache_0002 p0022 p0029
  have p0031 :=
    @g_vtoclg (.imp (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v)))) (.imp (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C))) v C (syn_cvv) dv_cache_0003 dv_cache_0004 p0012 p0030
  have p0032 :=
    @g_syl (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem C (syn_cvv)) (.imp (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C))) p0001 p0031
  have p0033 :=
    @g_mpd (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B) (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C)) p0000 p0032
  exact p0033

#print axioms g_opfvscl

end NFChoice.DirectNominalPrf.WPPReplay
