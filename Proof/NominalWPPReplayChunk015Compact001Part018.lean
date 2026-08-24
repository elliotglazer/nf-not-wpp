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
import NominalWPPReplayChunk015Compact001Part017

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

noncomputable def g_hwnisobaseextcl
    (A : Class) (B : Class) (C : Class) (D : Class) (hyp_hwnisobaseextcl_1 : Nominal.NPrf (syn_wss D A)) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_D, fresh_y_not_C, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_ne_y, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))
  have p0001 :=
    @g_elex B (syn_chwcn D)
  have p0002 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.classMem B (syn_chwcn D)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))
  have p0004 :=
    @g_elex C (syn_chwcn D)
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.classMem C (syn_chwcn D)) (.classMem C (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_eleq1 (.cv x) B (syn_chwcn D)
  have p0008 :=
    @g_biid (.classMem (.cv y) (syn_chwcn D))
  have p0009 :=
    @g_a1i (syn_wb (.classMem (.cv y) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.classEq (.cv x) B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) (syn_chwcn D)) (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)) p0007 p0009
  have p0011 :=
    @g_breq1 (.cv x) B (.cv y) (syn_chwniso D)
  have p0012 :=
    @g_breq1 (.cv x) B (.cv y) (syn_chwniso A)
  have p0013 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wbr (.cv x) (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y)) p0011 p0012
  have p0014 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wa (.classMem (.cv x) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.imp (syn_wbr (.cv x) (syn_chwniso D) (.cv y)) (syn_wbr (.cv x) (syn_chwniso A) (.cv y))) (.imp (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y))) p0010 p0013
  have p0015 :=
    @g_biid (.classMem B (syn_chwcn D))
  have p0016 :=
    @g_a1i (syn_wb (.classMem B (syn_chwcn D)) (.classMem B (syn_chwcn D))) (.classEq (.cv y) C) p0015
  have p0017 :=
    @g_eleq1 (.cv y) C (syn_chwcn D)
  have p0018 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem B (syn_chwcn D)) (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D)) (.classMem C (syn_chwcn D)) p0016 p0017
  have p0019 :=
    @g_breq2 (.cv y) C B (syn_chwniso D)
  have p0020 :=
    @g_breq2 (.cv y) C B (syn_chwniso A)
  have p0021 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) (.cv y)) (syn_wbr B (syn_chwniso A) C) p0019 p0020
  have p0022 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y))) (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C)) p0018 p0021
  have p0023 :=
    @g_hwnisobaseext y x A D dv_cache_0001 hyp_hwnisobaseextcl_1
  have p0024 :=
    @g_vtocl2g (.imp (syn_wa (.classMem (.cv x) (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.imp (syn_wbr (.cv x) (syn_chwniso D) (.cv y)) (syn_wbr (.cv x) (syn_chwniso A) (.cv y)))) (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem (.cv y) (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso D) (.cv y)) (syn_wbr B (syn_chwniso A) (.cv y)))) (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C))) x y B C (syn_cvv) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0014 p0022 p0023
  have p0025 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C))) p0006 p0024
  have p0026 :=
    @g_pm2_43i (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (.imp (syn_wbr B (syn_chwniso D) C) (syn_wbr B (syn_chwniso A) C)) p0025
  exact p0026

noncomputable def g_hwnisobasebicl
    (A : Class) (B : Class) (C : Class) (D : Class) (hyp_hwnisobasebicl_1 : Nominal.NPrf (syn_wss D A)) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_hwnisobaserestrcl A B C D
  have p0001 :=
    @g_hwnisobaseextcl A B C D hyp_hwnisobasebicl_1
  have p0002 :=
    @g_impbid (syn_wa (.classMem B (syn_chwcn D)) (.classMem C (syn_chwcn D))) (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwniso D) C) p0000 p0001
  exact p0002

noncomputable def g_hnqmap1basecompat
    (A : Class) (D : Class) (q : Var) (p : Var) (hyp_hnqmap1basecompat_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnqmap1basecompat_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnqmap1basecompat_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.imp (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ ({q} : Finset Var) ∪ ({p} : Finset Var)
  have p0000 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0001 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0002 :=
    @g_simprd (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0001
  have p0003 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0000 p0002
  have p0004 :=
    @g_fveq2d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_chnqmap1 A) p0003
  have p0005 :=
    @g_hwcnssbase A D hyp_hnqmap1basecompat_1
  have p0006 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0007 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0008 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0007
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0006 p0008
  have p0010 :=
    @g_sseldi (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv p)) p0005 p0009
  have p0011 :=
    @g_hnqmap1valcl A (syn_cuni (.cv p)) hyp_hnqmap1basecompat_3
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv p)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))) p0010 p0011
  have p0013 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv p)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) p0004 p0012
  have p0014 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) p0013
  have p0015 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0016 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0017 :=
    @g_simprd (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0016
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0015 p0017
  have p0019 :=
    @g_fveq2d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_chnqmap1 D) p0018
  have p0020 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0021 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0022 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0021
  have p0023 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0020 p0022
  have p0024 :=
    @g_hnqmap1valcl D (syn_cuni (.cv p)) hyp_hnqmap1basecompat_2
  have p0025 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv p)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))) p0023 p0024
  have p0026 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv p)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) p0019 p0025
  have p0027 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) p0026
  have p0028 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) p0027
  have p0029 :=
    @g_simpr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))
  have p0030 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)) p0028 p0029
  have p0031 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0032 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0033 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0032
  have p0034 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0031 p0033
  have p0035 :=
    @g_fveq2d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnqmap1 D) p0034
  have p0036 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0037 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0038 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0037
  have p0039 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0036 p0038
  have p0040 :=
    @g_hnqmap1valcl D (syn_cuni (.cv q)) hyp_hnqmap1basecompat_2
  have p0041 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv q)))) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) p0039 p0040
  have p0042 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_cfv (syn_chnqmap1 D) (.cv q)) (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv q)))) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) p0035 p0041
  have p0043 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) p0042
  have p0044 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cfv (syn_chnqmap1 D) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) p0030 p0043
  have p0045 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0046 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0047 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0046
  have p0048 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0045 p0047
  have p0049 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0050 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0051 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0050
  have p0052 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0049 p0051
  have p0053 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0048 p0052
  have p0054 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) p0053
  have p0055 :=
    @g_hwnisoclasseqbcl D (syn_cuni (.cv p)) (syn_cuni (.cv q)) hyp_hnqmap1basecompat_2
  have p0056 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D))) (syn_wb (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q)))) p0054 p0055
  have p0057 :=
    @g_biimpd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) p0056
  have p0058 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) p0044 p0057
  have p0059 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0060 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0061 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0060
  have p0062 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0059 p0061
  have p0063 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0064 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0065 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0064
  have p0066 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0063 p0065
  have p0067 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0062 p0066
  have p0068 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) p0067
  have p0069 :=
    @g_hwnisobaseextcl A (syn_cuni (.cv p)) (syn_cuni (.cv q)) D hyp_hnqmap1basecompat_1
  have p0070 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D))) (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q)))) p0068 p0069
  have p0071 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) p0058 p0070
  have p0072 :=
    @g_hwcnssbase A D hyp_hnqmap1basecompat_1
  have p0073 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0074 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0075 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0074
  have p0076 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0073 p0075
  have p0077 :=
    @g_sseldi (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv p)) p0072 p0076
  have p0078 :=
    @g_hwcnssbase A D hyp_hnqmap1basecompat_1
  have p0079 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0080 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0081 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0080
  have p0082 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0079 p0081
  have p0083 :=
    @g_sseldi (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv q)) p0078 p0082
  have p0084 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn A)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) p0077 p0083
  have p0085 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn A)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) p0084
  have p0086 :=
    @g_hwnisoclasseqbcl A (syn_cuni (.cv p)) (syn_cuni (.cv q)) hyp_hnqmap1basecompat_3
  have p0087 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn A)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A))) (syn_wb (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q)))) p0085 p0086
  have p0088 :=
    @g_biimprd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) p0087
  have p0089 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) p0071 p0088
  have p0090 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) p0014 p0089
  have p0091 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0092 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0093 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0092
  have p0094 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0091 p0093
  have p0095 :=
    @g_fveq2d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnqmap1 A) p0094
  have p0096 :=
    @g_hwcnssbase A D hyp_hnqmap1basecompat_1
  have p0097 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0098 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0099 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0098
  have p0100 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0097 p0099
  have p0101 :=
    @g_sseldi (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv q)) p0096 p0100
  have p0102 :=
    @g_hnqmap1valcl A (syn_cuni (.cv q)) hyp_hnqmap1basecompat_3
  have p0103 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv q)))) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) p0101 p0102
  have p0104 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv q)))) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) p0095 p0103
  have p0105 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) p0104
  have p0106 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) p0105
  have p0107 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q)))) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) (syn_cfv (syn_chnqmap1 A) (.cv q)) p0090 p0106
  have p0108 :=
    @g_ex (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) p0107
  exact p0108

noncomputable def g_hnqmap1basereflect
    (A : Class) (D : Class) (q : Var) (p : Var) (hyp_hnqmap1basereflect_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnqmap1basereflect_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnqmap1basereflect_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.imp (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ ({q} : Finset Var) ∪ ({p} : Finset Var)
  have p0000 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0001 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0002 :=
    @g_simprd (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0001
  have p0003 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0000 p0002
  have p0004 :=
    @g_fveq2d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_chnqmap1 D) p0003
  have p0005 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0006 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0007 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0006
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0005 p0007
  have p0009 :=
    @g_hnqmap1valcl D (syn_cuni (.cv p)) hyp_hnqmap1basereflect_2
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv p)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))) p0008 p0009
  have p0011 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv p)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) p0004 p0010
  have p0012 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) p0011
  have p0013 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0014 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0015 :=
    @g_simprd (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0014
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0013 p0015
  have p0017 :=
    @g_fveq2d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_chnqmap1 A) p0016
  have p0018 :=
    @g_hwcnssbase A D hyp_hnqmap1basereflect_1
  have p0019 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0020 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0021 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0020
  have p0022 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0019 p0021
  have p0023 :=
    @g_sseldi (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv p)) p0018 p0022
  have p0024 :=
    @g_hnqmap1valcl A (syn_cuni (.cv p)) hyp_hnqmap1basereflect_3
  have p0025 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv p)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))) p0023 p0024
  have p0026 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv p)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) p0017 p0025
  have p0027 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) p0026
  have p0028 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) p0027
  have p0029 :=
    @g_simpr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))
  have p0030 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)) p0028 p0029
  have p0031 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0032 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0033 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0032
  have p0034 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0031 p0033
  have p0035 :=
    @g_fveq2d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnqmap1 A) p0034
  have p0036 :=
    @g_hwcnssbase A D hyp_hnqmap1basereflect_1
  have p0037 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0038 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0039 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0038
  have p0040 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0037 p0039
  have p0041 :=
    @g_sseldi (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv q)) p0036 p0040
  have p0042 :=
    @g_hnqmap1valcl A (syn_cuni (.cv q)) hyp_hnqmap1basereflect_3
  have p0043 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv q)))) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) p0041 p0042
  have p0044 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cuni (.cv q)))) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) p0035 p0043
  have p0045 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) p0044
  have p0046 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A)) p0030 p0045
  have p0047 :=
    @g_hwcnssbase A D hyp_hnqmap1basereflect_1
  have p0048 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0049 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0050 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0049
  have p0051 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0048 p0050
  have p0052 :=
    @g_sseldi (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv p)) p0047 p0051
  have p0053 :=
    @g_hwcnssbase A D hyp_hnqmap1basereflect_1
  have p0054 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0055 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0056 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0055
  have p0057 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0054 p0056
  have p0058 :=
    @g_sseldi (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_chwcn D) (syn_chwcn A) (syn_cuni (.cv q)) p0053 p0057
  have p0059 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn A)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) p0052 p0058
  have p0060 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn A)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) p0059
  have p0061 :=
    @g_hwnisoclasseqbcl A (syn_cuni (.cv p)) (syn_cuni (.cv q)) hyp_hnqmap1basereflect_3
  have p0062 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn A)) (.classMem (syn_cuni (.cv q)) (syn_chwcn A))) (syn_wb (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q)))) p0060 p0061
  have p0063 :=
    @g_biimpd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) p0062
  have p0064 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso A)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso A))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) p0046 p0063
  have p0065 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0066 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0067 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0066
  have p0068 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0065 p0067
  have p0069 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0070 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0071 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0070
  have p0072 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0069 p0071
  have p0073 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0068 p0072
  have p0074 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) p0073
  have p0075 :=
    @g_hwnisobaserestrcl A (syn_cuni (.cv p)) (syn_cuni (.cv q)) D
  have p0076 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D))) (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q)))) p0074 p0075
  have p0077 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso A) (syn_cuni (.cv q))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) p0064 p0076
  have p0078 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0079 :=
    @g_hnwpw1argcl (syn_chwcn D) p
  have p0080 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0079
  have p0081 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) p0078 p0080
  have p0082 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0083 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0084 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0083
  have p0085 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0082 p0084
  have p0086 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0081 p0085
  have p0087 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) p0086
  have p0088 :=
    @g_hwnisoclasseqbcl D (syn_cuni (.cv p)) (syn_cuni (.cv q)) hyp_hnqmap1basereflect_2
  have p0089 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn D)) (.classMem (syn_cuni (.cv q)) (syn_chwcn D))) (syn_wb (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q)))) p0087 p0088
  have p0090 :=
    @g_biimprd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) p0089
  have p0091 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso D) (syn_cuni (.cv q))) (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) p0077 p0090
  have p0092 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv p)) (syn_chwniso D)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) p0012 p0091
  have p0093 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0094 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0095 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0094
  have p0096 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0093 p0095
  have p0097 :=
    @g_fveq2d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_chnqmap1 D) p0096
  have p0098 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))
  have p0099 :=
    @g_hnwpw1argcl (syn_chwcn D) q
  have p0100 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0099
  have p0101 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) p0098 p0100
  have p0102 :=
    @g_hnqmap1valcl D (syn_cuni (.cv q)) hyp_hnqmap1basereflect_2
  have p0103 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classMem (syn_cuni (.cv q)) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv q)))) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) p0101 p0102
  have p0104 :=
    @g_eqtrd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (syn_cfv (syn_chnqmap1 D) (.cv q)) (syn_cfv (syn_chnqmap1 D) (syn_csn (syn_cuni (.cv q)))) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) p0097 p0103
  have p0105 :=
    @g_adantr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) p0104
  have p0106 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_cfv (syn_chnqmap1 D) (.cv q)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) p0105
  have p0107 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q)))) (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cec (syn_cuni (.cv q)) (syn_chwniso D)) (syn_cfv (syn_chnqmap1 D) (.cv q)) p0092 p0106
  have p0108 :=
    @g_ex (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn D))) (.classMem (.cv q) (syn_cpw1 (syn_chwcn D)))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv p)) (syn_cfv (syn_chnqmap1 A) (.cv q))) (.classEq (syn_cfv (syn_chnqmap1 D) (.cv p)) (syn_cfv (syn_chnqmap1 D) (.cv q))) p0107
  exact p0108

noncomputable def g_hnqincexg
    (A : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv))) (.classMem (syn_chnqinc D A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  have p0000 :=
    (by simpa [syn_chnqinc] using (Nominal.classEqRefl (syn_chnqinc D A)))
  have p0001 :=
    @g_simpr (.classMem D (syn_cvv)) (.classMem A (syn_cvv))
  have p0002 :=
    @g_hnqmap1exg A
  have p0003 :=
    @g_syl (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv))) (.classMem A (syn_cvv)) (.classMem (syn_chnqmap1 A) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_simpl (.classMem D (syn_cvv)) (.classMem A (syn_cvv))
  have p0005 :=
    @g_hnqmap1exg D
  have p0006 :=
    @g_syl (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv))) (.classMem D (syn_cvv)) (.classMem (syn_chnqmap1 D) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_cnvexg (syn_chnqmap1 D) (syn_cvv)
  have p0008 :=
    @g_syl (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv))) (.classMem (syn_chnqmap1 D) (syn_cvv)) (.classMem (syn_ccnv (syn_chnqmap1 D)) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_jca (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv))) (.classMem (syn_chnqmap1 A) (syn_cvv)) (.classMem (syn_ccnv (syn_chnqmap1 D)) (syn_cvv)) p0003 p0008
  have p0010 :=
    @g_coexg (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_syl (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv))) (syn_wa (.classMem (syn_chnqmap1 A) (syn_cvv)) (.classMem (syn_ccnv (syn_chnqmap1 D)) (syn_cvv))) (.classMem (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_syl5eqel (syn_wa (.classMem D (syn_cvv)) (.classMem A (syn_cvv))) (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) (syn_cvv) p0000 p0011
  exact p0012

#print axioms g_hnqincexg

end NFChoice.DirectNominalPrf.WPPReplay
