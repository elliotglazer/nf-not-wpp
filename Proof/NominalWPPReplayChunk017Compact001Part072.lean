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
import NominalWPPReplayChunk017Compact001Part071

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

noncomputable def g_hnwcutcodecmpbrclndv
    (u : Var) (A : Class) (B : Class) (C : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint (({x} : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({x} : Finset Var)) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) (({u} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ u from (by exact fresh_x_ne_u)))))))), (show Disjoint (({x} : Finset Var)) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint (({x} : Finset Var)) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0002 : Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint (({y} : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({y} : Finset Var)) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) (({u} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show y ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ u from (by exact fresh_y_ne_u)))))))), (show Disjoint (({y} : Finset Var)) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint (({y} : Finset Var)) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0003 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0006 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_u, fresh_y_ne_x, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.imp (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_ne_u, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
  have p0001 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))
  have p0002 :=
    @g_simprd (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))) p0001
  have p0003 :=
    @g_simprd (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))) p0002
  have p0004 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))
  have p0005 :=
    @g_simprd (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))) p0004
  have p0006 :=
    @g_simpld (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))) p0005
  have p0007 :=
    @g_elex B (syn_cfv (syn_c2nd) (.cv u))
  have p0008 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem B (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_biid (.classMem C (syn_cfv (syn_c2nd) (.cv u)))
  have p0010 :=
    @g_a1i (syn_wb (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv x) B) p0009
  have p0011 :=
    @g_biid (.classMem A (syn_cvv))
  have p0012 :=
    @g_a1i (syn_wb (.classMem A (syn_cvv)) (.classMem A (syn_cvv))) (.classEq (.cv x) B) p0011
  have p0013 :=
    @g_biid (.classMem (.cv u) (syn_chwcn A))
  have p0014 :=
    @g_a1i (syn_wb (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv x) B) p0013
  have p0015 :=
    @g_id (.classEq (.cv x) B)
  have p0016 :=
    @g_eleq1d (.classEq (.cv x) B) (.cv x) B (syn_cfv (syn_c2nd) (.cv u)) p0015
  have p0017 :=
    @g_biid (.classMem C (syn_cfv (syn_c2nd) (.cv u)))
  have p0018 :=
    @g_a1i (syn_wb (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv x) B) p0017
  have p0019 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))) p0016 p0018
  have p0020 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))) p0014 p0019
  have p0021 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem A (syn_cvv)) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))))) p0012 p0020
  have p0022 :=
    @g_hnwcutcodeeq3 (.cv x) B (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001
  have p0023 :=
    @g_breq1d (.classEq (.cv x) B) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C) (syn_chncodecmpset A) p0022
  have p0024 :=
    @g_id (.classEq (.cv x) B)
  have p0025 :=
    @g_breq1d (.classEq (.cv x) B) (.cv x) B C (syn_cfv (syn_c1st) (.cv u)) p0024
  have p0026 :=
    @g_bibi12d (.classEq (.cv x) B) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C) (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C) p0023 p0025
  have p0027 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C)) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C)) p0021 p0026
  have p0028 :=
    @g_imbi12d (.classEq (.cv x) B) (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C))) (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))) p0010 p0027
  have p0029 :=
    @g_elex C (syn_cfv (syn_c2nd) (.cv u))
  have p0030 :=
    @g_biid (.classMem A (syn_cvv))
  have p0031 :=
    @g_a1i (syn_wb (.classMem A (syn_cvv)) (.classMem A (syn_cvv))) (.classEq (.cv y) C) p0030
  have p0032 :=
    @g_biid (.classMem (.cv u) (syn_chwcn A))
  have p0033 :=
    @g_a1i (syn_wb (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv y) C) p0032
  have p0034 :=
    @g_biid (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0035 :=
    @g_a1i (syn_wb (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv y) C) p0034
  have p0036 :=
    @g_id (.classEq (.cv y) C)
  have p0037 :=
    @g_eleq1d (.classEq (.cv y) C) (.cv y) C (syn_cfv (syn_c2nd) (.cv u)) p0036
  have p0038 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))) p0035 p0037
  have p0039 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))) p0033 p0038
  have p0040 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem A (syn_cvv)) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))))) p0031 p0039
  have p0041 :=
    @g_hnwcutcodeeq3 (.cv y) C (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0002
  have p0042 :=
    @g_breq2d (.classEq (.cv y) C) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) p0041
  have p0043 :=
    @g_id (.classEq (.cv y) C)
  have p0044 :=
    @g_breq2d (.classEq (.cv y) C) (.cv y) C (.cv x) (syn_cfv (syn_c1st) (.cv u)) p0043
  have p0045 :=
    @g_bibi12d (.classEq (.cv y) C) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C) p0042 p0044
  have p0046 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C)) p0040 p0045
  have p0047 :=
    @g_hnwcutcodecmpbrndv x y u A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0048 :=
    @g_vtoclg (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))) (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C))) y C (syn_cvv) dv_cache_0006 dv_cache_0007 p0046 p0047
  have p0049 :=
    @g_syl (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cvv)) (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C))) p0029 p0048
  have p0050 :=
    @g_vtoclg (.imp (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C)))) (.imp (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C)))) x B (syn_cvv) dv_cache_0008 dv_cache_0009 p0028 p0049
  have p0051 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem B (syn_cvv)) (.imp (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C)))) p0008 p0050
  have p0052 :=
    @g_mpd (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))) p0003 p0051
  have p0053 :=
    @g_mpd (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B) (syn_chncodecmpset A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)) (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C)) p0000 p0052
  exact p0053

noncomputable def g_pw12si2brndv
    (D : Class) (R : Class) (q : Var) (p : Var) (dv_R_p : p ∉ R.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi R)) (.cv q)) (syn_wbr (syn_cuni (syn_cuni (.cv p))) R (syn_cuni (syn_cuni (.cv q)))))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({q} : Finset Var) ∪ ({p} : Finset Var)
  have dv_cache_0001 : Disjoint ((syn_cuni (syn_cuni (.cv p)))).fv (R).fv := by
    exact (show Disjoint ((syn_cuni (syn_cuni (.cv p)))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((syn_cuni (.cv p))).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv p)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact dv_R_p))))))))))
  have p0000 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0001 :=
    @g_pw12argcl (.cv p) D
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) D) (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))))) p0000 p0001
  have p0003 :=
    @g_simprd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (syn_cuni (.cv p))) D) (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))) p0002
  have p0004 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0005 :=
    @g_pw12argcl (.cv q) D
  have p0006 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0004 p0005
  have p0007 :=
    @g_simprd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0008 :=
    @g_breq12d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))) (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csi (syn_csi R)) p0003 p0007
  have p0009 :=
    @g_snex (syn_cuni (syn_cuni (.cv p)))
  have p0010 :=
    @g_snex (syn_cuni (syn_cuni (.cv q)))
  have p0011 :=
    @g_brsnsi (syn_csn (syn_cuni (syn_cuni (.cv p)))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csi R) p0009 p0010
  have p0012 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))) (syn_csi (syn_csi R)) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_wbr (syn_csn (syn_cuni (syn_cuni (.cv p)))) (syn_csi R) (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) p0011
  have p0013 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0014 :=
    @g_elex (.cv p) (syn_cpw1 (syn_cpw1 D))
  have p0015 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv p) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_uniexg (.cv p) (syn_cvv)
  have p0017 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv p) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv)) p0015 p0016
  have p0018 :=
    @g_uniexg (syn_cuni (.cv p)) (syn_cvv)
  have p0019 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (.cv p)) (syn_cvv)) (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cvv)) p0017 p0018
  have p0020 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0021 :=
    @g_elex (.cv q) (syn_cpw1 (syn_cpw1 D))
  have p0022 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_uniexg (.cv q) (syn_cvv)
  have p0024 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv q) (syn_cvv)) (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0022 p0023
  have p0025 :=
    @g_uniexg (syn_cuni (.cv q)) (syn_cvv)
  have p0026 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv)) p0024 p0025
  have p0027 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cvv)) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv)) p0019 p0026
  have p0028 :=
    @g_brsnsiandv (syn_cuni (syn_cuni (.cv p))) (syn_cuni (syn_cuni (.cv q))) R dv_cache_0001
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cvv)) (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv))) (syn_wb (syn_wbr (syn_csn (syn_cuni (syn_cuni (.cv p)))) (syn_csi R) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_wbr (syn_cuni (syn_cuni (.cv p))) R (syn_cuni (syn_cuni (.cv q))))) p0027 p0028
  have p0030 :=
    @g_n_3bitrd (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv p) (syn_csi (syn_csi R)) (.cv q)) (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))) (syn_csi (syn_csi R)) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) (syn_wbr (syn_csn (syn_cuni (syn_cuni (.cv p)))) (syn_csi R) (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_wbr (syn_cuni (syn_cuni (.cv p))) R (syn_cuni (syn_cuni (.cv q)))) p0008 p0012 p0029
  exact p0030

#print axioms g_pw12si2brndv

end NFChoice.DirectNominalPrf.WPPReplay
