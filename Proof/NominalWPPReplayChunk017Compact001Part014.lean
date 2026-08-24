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
import NominalWPPReplayChunk017Compact001Part013

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

noncomputable def g_wppqkrelcanonicalfiberndv
    (A : Class) (B : Class) (D : Class) (hyp_wppqkrelcanonicalfiberndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_wppqkrelcanonicalfiberndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_wppqkrelcanonicalfiberndv_3 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq D (syn_copk A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ D.fv
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
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
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
  have dv_cache_0001 : x ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ ((Wff.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq D (syn_copk A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq D (syn_copk A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_opex A B hyp_wppqkrelcanonicalfiberndv_1 hyp_wppqkrelcanonicalfiberndv_2
  have p0001 :=
    @g_wppqkrelkernelrangeformndv (syn_cop A B) D p0000 hyp_wppqkrelcanonicalfiberndv_3
  have p0002 :=
    @g_elxpk x y D (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0003 :=
    @g_biimpi (.classMem D (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wex x (syn_wex y (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))) p0002
  have p0004 :=
    @g_syl (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (.classMem D (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wex x (syn_wex y (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))) p0001 p0003
  have p0005 :=
    @g_nfv (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) x dv_cache_0006
  have p0006 :=
    @g_nfv (.classEq D (syn_copk A B)) x dv_cache_0007
  have p0007 :=
    @g_nfv (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) y dv_cache_0008
  have p0008 :=
    @g_nfv (.classEq D (syn_copk A B)) y dv_cache_0009
  have p0009 :=
    @g_simpr (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
  have p0010 :=
    @g_simpl (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
  have p0011 :=
    @g_syl (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq D (syn_copk (.cv x) (.cv y))) p0009 p0010
  have p0012 :=
    @g_simpl (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
  have p0013 :=
    @g_simpr (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
  have p0014 :=
    @g_simpl (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
  have p0015 :=
    @g_syl (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq D (syn_copk (.cv x) (.cv y))) p0013 p0014
  have p0016 :=
    @g_opeq2d (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) D (syn_copk (.cv x) (.cv y)) (syn_csn (syn_csn (syn_cop A B))) p0015
  have p0017 :=
    @g_eleq1d (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk (.cv x) (.cv y))) (syn_ckqrel (syn_cwppqkrelkernel)) p0016
  have p0018 :=
    @g_mpbid (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk (.cv x) (.cv y))) (syn_ckqrel (syn_cwppqkrelkernel))) p0012 p0017
  have p0019 :=
    @g_opex A B hyp_wppqkrelcanonicalfiberndv_1 hyp_wppqkrelcanonicalfiberndv_2
  have p0020 :=
    @g_vex x
  have p0021 :=
    @g_vex y
  have p0022 :=
    @g_wppqkrelkernelpointbrndv (syn_cop A B) (.cv x) (.cv y) p0019 p0020 p0021
  have p0023 :=
    @g_biimpi (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk (.cv x) (.cv y))) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) p0022
  have p0024 :=
    @g_syl (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk (.cv x) (.cv y))) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) p0018 p0023
  have p0025 :=
    @g_opth A B (.cv x) (.cv y)
  have p0026 :=
    @g_biimpi (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) (syn_wa (.classEq A (.cv x)) (.classEq B (.cv y))) p0025
  have p0027 :=
    @g_syl (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) (syn_wa (.classEq A (.cv x)) (.classEq B (.cv y))) p0024 p0026
  have p0028 :=
    @g_opkeq12 A B (.cv x) (.cv y)
  have p0029 :=
    @g_syl (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (syn_wa (.classEq A (.cv x)) (.classEq B (.cv y))) (.classEq (syn_copk A B) (syn_copk (.cv x) (.cv y))) p0027 p0028
  have p0030 :=
    @g_eqcomd (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (syn_copk A B) (syn_copk (.cv x) (.cv y)) p0029
  have p0031 :=
    @g_eqtrd (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) D (syn_copk (.cv x) (.cv y)) (syn_copk A B) p0011 p0030
  have p0032 :=
    @g_ex (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq D (syn_copk A B)) p0031
  have p0033 :=
    @g_exlimd (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) (.classEq D (syn_copk A B)) y p0007 p0008 p0032
  have p0034 :=
    @g_exlimd (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wex y (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))) (.classEq D (syn_copk A B)) x p0005 p0006 p0033
  have p0035 :=
    @g_mpd (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wex x (syn_wex y (syn_wa (.classEq D (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))) (.classEq D (syn_copk A B)) p0004 p0034
  have p0036 :=
    @g_eqid (syn_cop A B)
  have p0037 :=
    @g_opex A B hyp_wppqkrelcanonicalfiberndv_1 hyp_wppqkrelcanonicalfiberndv_2
  have p0038 :=
    @g_wppqkrelkernelpointbrndv (syn_cop A B) A B p0037 hyp_wppqkrelcanonicalfiberndv_1 hyp_wppqkrelcanonicalfiberndv_2
  have p0039 :=
    @g_mpbir (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk A B)) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq (syn_cop A B) (syn_cop A B)) p0036 p0038
  have p0040 :=
    @g_a1i (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk A B)) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq D (syn_copk A B)) p0039
  have p0041 :=
    @g_id (.classEq D (syn_copk A B))
  have p0042 :=
    @g_opeq2d (.classEq D (syn_copk A B)) D (syn_copk A B) (syn_csn (syn_csn (syn_cop A B))) p0041
  have p0043 :=
    @g_eleq1d (.classEq D (syn_copk A B)) (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk A B)) (syn_ckqrel (syn_cwppqkrelkernel)) p0042
  have p0044 :=
    @g_mpbird (.classEq D (syn_copk A B)) (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk A B)) (syn_ckqrel (syn_cwppqkrelkernel))) p0040 p0043
  have p0045 :=
    @g_impbii (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq D (syn_copk A B)) p0035 p0044
  exact p0045

noncomputable def g_wppqkrelcanonicaleu
    (A : Class) (B : Class) (d : Var) (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (hyp_wppqkrelcanonicaleu_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_wppqkrelcanonicaleu_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_weu d (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({d} : Finset Var)
  have dv_cache_0001 : d ∉ ((syn_copk A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_d, dv_B_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_opkex A B
  have p0001 :=
    @g_eueq1 d (syn_copk A B) dv_cache_0001 p0000
  have p0002 :=
    @g_vex d
  have p0003 :=
    @g_wppqkrelcanonicalfiberndv A B (.cv d) hyp_wppqkrelcanonicaleu_1 hyp_wppqkrelcanonicaleu_2 p0002
  have p0004 :=
    @g_eubii (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq (.cv d) (syn_copk A B)) d p0003
  have p0005 :=
    @g_mpbir (syn_weu d (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) (syn_weu d (.classEq (.cv d) (syn_copk A B))) p0001 p0004
  exact p0005

noncomputable def g_wppqkrelresfnndv
    (A : Class) (B : Class) (hyp_wppqkrelresfnndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_wppqkrelresfnndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let s : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_s_ne_d : s ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_s : d ≠ s :=
    Ne.symm fresh_s_ne_d
  have fresh_s_ne_u : s ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_s : u ≠ s :=
    Ne.symm fresh_s_ne_u
  have fresh_s_ne_a : s ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_s : a ≠ s :=
    Ne.symm fresh_s_ne_a
  have fresh_s_ne_b : s ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_s : b ≠ s :=
    Ne.symm fresh_s_ne_b
  have fresh_d_ne_u : d ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_d : u ≠ d :=
    Ne.symm fresh_d_ne_u
  have fresh_d_ne_a : d ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_d : a ≠ d :=
    Ne.symm fresh_d_ne_a
  have fresh_d_ne_b : d ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_d : b ≠ d :=
    Ne.symm fresh_d_ne_b
  have fresh_u_ne_a : u ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_u : a ≠ u :=
    Ne.symm fresh_u_ne_a
  have fresh_u_ne_b : u ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_u : b ≠ u :=
    Ne.symm fresh_u_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : u ∉ ((Class.cv s)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0010 : a ∉ ((syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_s, fresh_a_not_A, fresh_a_not_B, fresh_a_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_s, fresh_a_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_s, fresh_b_not_A, fresh_b_not_B, fresh_b_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ ((syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_s, fresh_b_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : d ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : d ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : d ∉ ((syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_s, fresh_d_not_A, fresh_d_not_B, fresh_d_ne_u, fresh_d_ne_a, fresh_d_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : u ∉ ((syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_s, fresh_u_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : u ∉ ((Wff.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_s, fresh_u_not_A, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : s ∉ ((syn_cpw1 (syn_cpw1 (syn_cxp A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, fresh_s_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : d ∉ ((syn_cpw1 (syn_cpw1 (syn_cxp A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : s ∉ ((syn_ckqrel (syn_cwppqkrelkernel))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : d ∉ ((syn_ckqrel (syn_cwppqkrelkernel))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : s ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show s ≠ d from (by exact fresh_s_ne_d))
  have p0000 :=
    @g_elpw12 u (.cv s) (syn_cxp A B) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) p0000
  have p0002 :=
    @g_simpl (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0003 :=
    @g_simpr (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))
  have p0004 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classMem (.cv u) (syn_cxp A B)) p0002 p0003
  have p0005 :=
    @g_elxp a b (.cv u) A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0006 :=
    @g_biimpi (.classMem (.cv u) (syn_cxp A B)) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))) p0005
  have p0007 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (.classMem (.cv u) (syn_cxp A B)) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))) p0004 p0006
  have p0008 :=
    @g_nfv (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) a dv_cache_0010
  have p0009 :=
    @g_nfv (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) a dv_cache_0011
  have p0010 :=
    @g_nfv (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) b dv_cache_0012
  have p0011 :=
    @g_nfv (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) b dv_cache_0013
  have p0012 :=
    @g_vex a
  have p0013 :=
    @g_vex b
  have p0014 :=
    @g_wppqkrelcanonicaleu (.cv a) (.cv b) d dv_cache_0014 dv_cache_0015 p0012 p0013
  have p0015 :=
    @g_a1i (syn_weu d (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) p0014
  have p0016 :=
    @g_nfv (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) d dv_cache_0016
  have p0017 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0018 :=
    @g_simpr (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) p0017 p0018
  have p0020 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0021 :=
    @g_simpl (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))) (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) p0020 p0021
  have p0023 :=
    @g_sneq (.cv u) (syn_cop (.cv a) (.cv b))
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (.classEq (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b)))) p0022 p0023
  have p0025 :=
    @g_sneq (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b)))
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classEq (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b)))) (.classEq (syn_csn (syn_csn (.cv u))) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b))))) p0024 p0025
  have p0027 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.cv s) (syn_csn (syn_csn (.cv u))) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) p0019 p0026
  have p0028 :=
    @g_opeq1d (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.cv s) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d) p0027
  have p0029 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_cop (.cv s) (.cv d)) (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)) p0028
  have p0030 :=
    @g_eubid (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) d p0016 p0029
  have p0031 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) (syn_weu d (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) p0015 p0030
  have p0032 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) p0031
  have p0033 :=
    @g_exlimd (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) b p0010 p0011 p0032
  have p0034 :=
    @g_exlimd (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) a p0008 p0009 p0033
  have p0035 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) p0007 p0034
  have p0036 :=
    @g_ex (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) p0035
  have p0037 :=
    @g_rexlimdva (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) u (syn_cxp A B) dv_cache_0017 dv_cache_0018 p0036
  have p0038 :=
    @g_mpd (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) p0001 p0037
  have p0039 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))))
  have p0040 :=
    @g_eubii (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) d p0039
  have p0041 :=
    @g_a1i (syn_wb (syn_weu d (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) p0040
  have p0042 :=
    @g_mpbird (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_weu d (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))) (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))) p0038 p0041
  have p0043 :=
    @g_rgen (syn_weu d (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))) s (syn_cpw1 (syn_cpw1 (syn_cxp A B))) p0042
  have p0044 :=
    @g_fnres s d (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_ckqrel (syn_cwppqkrelkernel)) dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
  have p0045 :=
    @g_mpbir (syn_wfn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wral s (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_weu d (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)))) p0043 p0044
  exact p0045

#print axioms g_wppqkrelresfnndv

end NFChoice.DirectNominalPrf.WPPReplay
