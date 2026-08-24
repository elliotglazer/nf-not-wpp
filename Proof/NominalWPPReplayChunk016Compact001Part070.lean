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
import NominalWPPReplayChunk016Compact001Part069

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

noncomputable def g_hwnisodirectisobndv
    (v : Var) (u : Var) (A : Class) (h : Var) (dv_A_h : h ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({h} : Finset Var)
  have dv_cache_0001 : u ≠ v := by
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0002 : h ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002
    exact (show h ≠ u from (by exact dv_h_u))
  have dv_cache_0004 : h ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ v from (by exact dv_h_v))
  have p0000 :=
    @g_hwnisohwisob v u A dv_cache_0001
  have p0001 :=
    @g_a1i (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0000
  have p0002 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0003 :=
    @g_a1i (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0002
  have p0004 :=
    @g_pm3_2 (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0005 :=
    @g_impbid (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0003 p0004
  have p0006 :=
    @g_bitrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0001 p0005
  have p0007 :=
    @g_brhwisoany v u A h dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0008 :=
    @g_a1i (syn_wb (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0007
  have p0009 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0010 :=
    @g_a1i (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0009
  have p0011 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0012 :=
    @g_hwcnraw u A
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) p0011 p0012
  have p0014 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0015 :=
    @g_hwcnraw v A
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcodes A)) p0014 p0015
  have p0017 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)) p0013 p0016
  have p0018 :=
    @g_pm3_2 (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0019 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (.imp (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) p0017 p0018
  have p0020 :=
    @g_impbid (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0010 p0019
  have p0021 :=
    @g_bitrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0008 p0020
  have p0022 :=
    @g_bitrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0006 p0021
  exact p0022

noncomputable def g_hwnisodirectisobclndv
    (A : Class) (B : Class) (C : Class) (h : Var) (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) (dv_C_h : h ∉ C.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))) := by
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
  have dv_cache_0006 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0007 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((Wff.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A, fresh_u_ne_v, fresh_u_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : v ∉ ((Wff.imp (.classMem B (syn_cvv)) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_A, fresh_v_not_C, fresh_v_ne_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0001 :=
    @g_elex B (syn_chwcn A)
  have p0002 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0004 :=
    @g_elex C (syn_chwcn A)
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_biid (.classMem B (syn_cvv))
  have p0007 :=
    @g_a1i (syn_wb (.classMem B (syn_cvv)) (.classMem B (syn_cvv))) (.classEq (.cv v) C) p0006
  have p0008 :=
    @g_biid (.classMem B (syn_chwcn A))
  have p0009 :=
    @g_a1i (syn_wb (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A))) (.classEq (.cv v) C) p0008
  have p0010 :=
    @g_id (.classEq (.cv v) C)
  have p0011 :=
    @g_eleq1d (.classEq (.cv v) C) (.cv v) C (syn_chwcn A) p0010
  have p0012 :=
    @g_anbi12d (.classEq (.cv v) C) (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem C (syn_chwcn A)) p0009 p0011
  have p0013 :=
    @g_id (.classEq (.cv v) C)
  have p0014 :=
    @g_breq2d (.classEq (.cv v) C) (.cv v) C B (syn_chwniso A) p0013
  have p0015 :=
    @g_id (.classEq (.cv v) C)
  have p0016 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c1st) p0015
  have p0017 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (.cv h)
  have p0018 :=
    @g_syl (.classEq (.cv v) C) (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C)) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) p0016 p0017
  have p0019 :=
    @g_id (.classEq (.cv v) C)
  have p0020 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c2nd) p0019
  have p0021 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (.cv h)
  have p0022 :=
    @g_syl (.classEq (.cv v) C) (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C)) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) p0020 p0021
  have p0023 :=
    @g_bitrd (.classEq (.cv v) C) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)) p0018 p0022
  have p0024 :=
    @g_exbidv (.classEq (.cv v) C) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)) h dv_cache_0001 p0023
  have p0025 :=
    @g_bibi12d (.classEq (.cv v) C) (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))) p0014 p0024
  have p0026 :=
    @g_imbi12d (.classEq (.cv v) C) (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))) p0012 p0025
  have p0027 :=
    @g_imbi12d (.classEq (.cv v) C) (.classMem B (syn_cvv)) (.classMem B (syn_cvv)) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))) p0007 p0026
  have p0028 :=
    @g_id (.classEq (.cv u) B)
  have p0029 :=
    @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0028
  have p0030 :=
    @g_biid (.classMem (.cv v) (syn_chwcn A))
  have p0031 :=
    @g_a1i (syn_wb (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classEq (.cv u) B) p0030
  have p0032 :=
    @g_anbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0029 p0031
  have p0033 :=
    @g_id (.classEq (.cv u) B)
  have p0034 :=
    @g_breq1d (.classEq (.cv u) B) (.cv u) B (.cv v) (syn_chwniso A) p0033
  have p0035 :=
    @g_id (.classEq (.cv u) B)
  have p0036 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c1st) p0035
  have p0037 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B) (.cv h)
  have p0038 :=
    @g_syl (.classEq (.cv u) B) (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B)) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) p0036 p0037
  have p0039 :=
    @g_id (.classEq (.cv u) B)
  have p0040 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0039
  have p0041 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0042 :=
    @g_syl (.classEq (.cv u) B) (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B)) (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) p0040 p0041
  have p0043 :=
    @g_bitrd (.classEq (.cv u) B) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) p0038 p0042
  have p0044 :=
    @g_exbidv (.classEq (.cv u) B) (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))) h dv_cache_0002 p0043
  have p0045 :=
    @g_bibi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))) p0034 p0044
  have p0046 :=
    @g_imbi12d (.classEq (.cv u) B) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))) p0032 p0045
  have p0047 :=
    @g_hwnisodirectisobndv v u A h dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0048 :=
    @g_vtoclg (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))) u B (syn_cvv) dv_cache_0007 dv_cache_0008 p0046 p0047
  have p0049 :=
    @g_vtoclg (.imp (.classMem B (syn_cvv)) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))))) (.imp (.classMem B (syn_cvv)) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))))) v C (syn_cvv) dv_cache_0009 dv_cache_0010 p0027 p0048
  have p0050 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem C (syn_cvv)) (.imp (.classMem B (syn_cvv)) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))))) p0005 p0049
  have p0051 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_cvv)) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))) p0002 p0050
  have p0052 :=
    @g_pm2_43i (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))) p0051
  exact p0052

#print axioms g_hwnisodirectisobclndv

end NFChoice.DirectNominalPrf.WPPReplay
