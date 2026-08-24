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
import NominalWPPReplayChunk017Compact001Part069

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

noncomputable def g_wppconcrete6stoppedgammacontrgrowthstagedndv
    (y : Var) (hyp_wppconcrete6stoppedgammacontrgrowthstagedndv_1 : Nominal.NPrf (.neg (syn_wbr (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) :
    Nominal.NPrf (.imp (syn_wral y (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))))) (.neg (.classEq (syn_c0c) (syn_c0c)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var)
  let x : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact fresh_x (Finset.mem_singleton.mpr h)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact fresh_p (Finset.mem_singleton.mpr h)
  have fresh_y_ne_p : y ≠ p :=
    Ne.symm fresh_p_ne_y
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have dv_cache_0001 : p ∉ ((syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_cwppconcrete6fn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cwppconcrete6fn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cwppconcrete6fn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0008 : p ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show p ≠ y from (by exact fresh_p_ne_y))
  have dv_cache_0009 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_wppconcrete6fnfunsndv
  have p0001 :=
    @g_wppconcrete6rnhwcardsndv
  have p0002 :=
    @g_wppconcrete6thresholdhwcardsndv
  have p0003 :=
    @g_wppconcrete6thresholdtclecndv
  have p0004 :=
    @g_wppconcrete6hncard1dmcovndv p
  have p0005 :=
    @g_wppconcrete6stoppedtchomfullndv x
  have p0006 :=
    @g_wppconcrete6globalnonfixedfromhnshiftndv y hyp_wppconcrete6stoppedgammacontrgrowthstagedndv_1
  have p0007 :=
    @g_wppstopgammacontrgrowthstagedndv x y (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0000 p0001 p0002 p0003 p0004 p0005 p0006
  exact p0007

noncomputable def g_hnwcutcodeselfnoisoclndv
    (x : Var) (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))) (.neg (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((Wff.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))) (.neg (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_A, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)))
  have p0001 :=
    @g_simpl (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))
  have p0002 :=
    @g_elex B (syn_chwcn A)
  have p0003 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))) (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_id (.classEq (.cv v) B)
  have p0005 :=
    @g_eleq1d (.classEq (.cv v) B) (.cv v) B (syn_chwcn A) p0004
  have p0006 :=
    @g_id (.classEq (.cv v) B)
  have p0007 :=
    @g_fveq2d (.classEq (.cv v) B) (.cv v) B (syn_c2nd) p0006
  have p0008 :=
    @g_eleq2d (.classEq (.cv v) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) B) (.cv x) p0007
  have p0009 :=
    @g_anbi12d (.classEq (.cv v) B) (.classMem (.cv v) (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (.classMem (.cv x) (syn_cfv (syn_c2nd) B)) p0005 p0008
  have p0010 :=
    @g_id (.classEq (.cv v) B)
  have p0011 :=
    @g_id (.classEq (.cv v) B)
  have p0012 :=
    @g_fveq2d (.classEq (.cv v) B) (.cv v) B (syn_c1st) p0011
  have p0013 :=
    @g_id (.classEq (.cv v) B)
  have p0014 :=
    @g_fveq2d (.classEq (.cv v) B) (.cv v) B (syn_c2nd) p0013
  have p0015 :=
    @g_jca (.classEq (.cv v) B) (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B)) (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) B)) p0012 p0014
  have p0016 :=
    @g_hnwcutcodeeq12ndv x (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
  have p0017 :=
    @g_syl (.classEq (.cv v) B) (syn_wa (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B)) (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) B))) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x))) p0015 p0016
  have p0018 :=
    @g_breq12d (.classEq (.cv v) B) (.cv v) B (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x)) (syn_chwniso A) p0010 p0017
  have p0019 :=
    @g_notbid (.classEq (.cv v) B) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x))) p0018
  have p0020 :=
    @g_imbi12d (.classEq (.cv v) B) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))) (.neg (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.neg (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x)))) p0009 p0019
  have p0021 :=
    @g_hnwcutcodeselfnoisondv x v A dv_cache_0001
  have p0022 :=
    @g_vtoclg (.imp (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.neg (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))) (.neg (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x))))) v B (syn_cvv) dv_cache_0002 dv_cache_0003 p0020 p0021
  have p0023 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))) (.classMem B (syn_cvv)) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))) (.neg (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x))))) p0003 p0022
  have p0024 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) B))) (.neg (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (.cv x)))) p0000 p0023
  exact p0024

#print axioms g_hnwcutcodeselfnoisoclndv

end NFChoice.DirectNominalPrf.WPPReplay
