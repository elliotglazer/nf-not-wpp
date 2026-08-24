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
import NominalWPPReplayChunk014Compact001Part011

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

noncomputable def g_kqrelbr
    (A : Class) (B : Class) (C : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_B_C : Disjoint B.fv C.fv) (hyp_kqrelbr_1 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_kqrelbr_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop B C) (syn_ckqrel A)) (.classMem (syn_copk B C) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_x_not_C : x ∉ C.fv := by
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
  have fresh_y_not_C : y ∉ C.fv := by
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
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (syn_copk B C) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classMem (syn_copk B C) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_C, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_kqrel x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eleq2i (syn_ckqrel A) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A)) (syn_cop B C) p0000
  have p0002 :=
    @g_opkeq1 (.cv x) B (.cv y)
  have p0003 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_copk (.cv x) (.cv y)) (syn_copk B (.cv y)) A p0002
  have p0004 :=
    @g_opkeq2 (.cv y) C B
  have p0005 :=
    @g_eleq1d (.classEq (.cv y) C) (syn_copk B (.cv y)) (syn_copk B C) A p0004
  have p0006 :=
    @g_opelopab (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk B (.cv y)) A) (.classMem (syn_copk B C) A) x y B C dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0003 hyp_kqrelbr_1 hyp_kqrelbr_2 p0003 p0005
  have p0007 :=
    @g_bitri (.classMem (syn_cop B C) (syn_ckqrel A)) (.classMem (syn_cop B C) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A))) (.classMem (syn_copk B C) A) p0001 p0006
  exact p0007

noncomputable def g_fdminvalpex
    (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) (hyp_fdminvalpex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdminvalpex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdminvalpex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdminvalp R A B C) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cfdminvalp] using (Nominal.classEqRefl (syn_cfdminvalp R A B C)))
  have p0001 :=
    @g_fdminsepex A B R hyp_fdminvalpex_1 hyp_fdminvalpex_2 hyp_fdminvalpex_3
  have p0002 :=
    @g_cnvkex (syn_cfdminsep R A B) p0001
  have p0003 :=
    @g_snex C
  have p0004 :=
    @g_imakex (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C) p0002 p0003
  have p0005 :=
    @g_uni1ex (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) p0004
  have p0006 :=
    @g_eqeltri (syn_cfdminvalp R A B C) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_fdminvalpbr
    (z : Var) (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_z : z ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_z : z ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_z : z ∉ C.fv) (dv_R_z : z ∉ R.fv) (hyp_fdminvalpbr_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (.cv z) (syn_cfdminvalp R A B C)) (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfdminsep R A B))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cfdminvalp] using (Nominal.classEqRefl (syn_cfdminvalp R A B C)))
  have p0001 :=
    @g_eleq2i (syn_cfdminvalp R A B C) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (.cv z) p0000
  have p0002 :=
    @g_vex z
  have p0003 :=
    @g_eluni1 (.cv z) (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) p0002
  have p0004 :=
    @g_bitri (.classMem (.cv z) (syn_cfdminvalp R A B C)) (.classMem (.cv z) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)))) (.classMem (syn_csn (.cv z)) (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) p0001 p0003
  have p0005 :=
    @g_snex (.cv z)
  have p0006 :=
    @g_elimaksn (syn_ccnvk (syn_cfdminsep R A B)) C (syn_csn (.cv z)) hyp_fdminvalpbr_1 p0005
  have p0007 :=
    @g_bitri (.classMem (.cv z) (syn_cfdminvalp R A B C)) (.classMem (syn_csn (.cv z)) (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (.classMem (syn_copk C (syn_csn (.cv z))) (syn_ccnvk (syn_cfdminsep R A B))) p0004 p0006
  have p0008 :=
    @g_snex (.cv z)
  have p0009 :=
    @g_opkelcnvk C (syn_csn (.cv z)) (syn_cfdminsep R A B) hyp_fdminvalpbr_1 p0008
  have p0010 :=
    @g_bitri (.classMem (.cv z) (syn_cfdminvalp R A B C)) (.classMem (syn_copk C (syn_csn (.cv z))) (syn_ccnvk (syn_cfdminsep R A B))) (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfdminsep R A B)) p0007 p0009
  exact p0010

noncomputable def g_fdminqex
    (A : Class) (B : Class) (R : Class) (hyp_fdminqex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdminqex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdminqex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdminq R A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cfdminq] using (Nominal.classEqRefl (syn_cfdminq R A B)))
  have p0001 :=
    @g_fdminsepex A B R hyp_fdminqex_1 hyp_fdminqex_2 hyp_fdminqex_3
  have p0002 :=
    @g_kqrelex (syn_cfdminsep R A B) p0001
  have p0003 :=
    @g_eqeltri (syn_cfdminq R A B) (syn_ckqrel (syn_cfdminsep R A B)) (syn_cvv) p0000 p0002
  exact p0003

noncomputable def g_fdpivmap2ex
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdpivmap2 R A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p_ne_z : p ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_p : z ≠ p :=
    Ne.symm fresh_p_ne_z
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint ((syn_cfdminsep R A B)).fv ((syn_csn (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint ((syn_cfdminsep R A B)).fv ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (((Class.cv z)).fv) from (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(show Disjoint ((A).fv) (((Class.cv z)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({z} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show z ∉ (A).fv from (by exact fresh_z_not_A)))))), (show Disjoint ((B).fv) (((Class.cv z)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({z} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show z ∉ (B).fv from (by exact fresh_z_not_B))))))⟩), (show Disjoint ((R).fv) (((Class.cv z)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((R).fv) (({z} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show z ∉ (R).fv from (by exact fresh_z_not_R))))))⟩))))
  have dv_cache_0008 : Disjoint ((syn_cfdminsep R A B)).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint ((syn_cfdminsep R A B)).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (({p} : Finset Var)) from (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact fresh_p_not_A)))), (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact fresh_p_not_B))))⟩), (show Disjoint ((R).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))⟩))))
  have dv_cache_0009 : Disjoint ((syn_csn (.cv z))).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint ((syn_csn (.cv z))).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (((Class.cv z)).fv) (({p} : Finset Var)) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({z} : Finset Var)) (({p} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show z ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ p from (by exact fresh_z_ne_p))))))))))
  have dv_cache_0010 : Disjoint (A).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint (A).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0011 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : Disjoint (B).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint (B).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0013 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : Disjoint ((Class.cv p)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show Disjoint ((Class.cv p)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0015 : z ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((syn_cxpk B B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_cfdminq R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_cfdminq R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((syn_cfdminvalp R A B (.cv p))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_p, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : p ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show p ≠ z from (by exact fresh_p_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    (by simpa [syn_cfdminq] using (Nominal.classEqRefl (syn_cfdminq R A B)))
  have p0002 :=
    @g_eleq2i (syn_cfdminq R A B) (syn_ckqrel (syn_cfdminsep R A B)) (syn_cop (syn_csn (.cv z)) (.cv p)) p0001
  have p0003 :=
    @g_snex (.cv z)
  have p0004 :=
    @g_vex p
  have p0005 :=
    @g_kqrelbr (syn_cfdminsep R A B) (syn_csn (.cv z)) (.cv p) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0003 p0004
  have p0006 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_cfdminq R A B)) (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_ckqrel (syn_cfdminsep R A B))) (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) p0002 p0005
  have p0007 :=
    @g_vex p
  have p0008 :=
    @g_fdminvalpbr z A B (.cv p) R dv_cache_0001 dv_cache_0010 dv_cache_0002 dv_cache_0011 dv_cache_0012 dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 p0007
  have p0009 :=
    @g_bicomi (.classMem (.cv z) (syn_cfdminvalp R A B (.cv p))) (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) p0008
  have p0010 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_cfdminq R A B)) (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) (.classMem (.cv z) (syn_cfdminvalp R A B (.cv p))) p0006 p0009
  have p0011 :=
    @g_releqmpt p z (syn_cxpk B B) (syn_cfdminq R A B) (syn_cfdminvalp R A B (.cv p)) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0010
  have p0012 :=
    @g_eqtr4i (syn_cfdpivmap2 R A B) (syn_cmpt p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p))) (syn_cin (syn_cxp (syn_cxpk B B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdminq R A B))) (syn_c1c))))) p0000 p0011
  have p0013 :=
    @g_xpkex B B hyp_fdpivmap2ex_3 hyp_fdpivmap2ex_3
  have p0014 :=
    @g_fdminqex A B R hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0015 :=
    @g_mptexlem (syn_cxpk B B) (syn_cfdminq R A B) p0013 p0014
  have p0016 :=
    @g_eqeltri (syn_cfdpivmap2 R A B) (syn_cin (syn_cxp (syn_cxpk B B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdminq R A B))) (syn_c1c))))) (syn_cvv) p0012 p0015
  exact p0016

noncomputable def g_fdpivmap2fn
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cfdpivmap2 R A B) (syn_cxpk B B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv p)).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0005 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint ((Class.cv p)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint ((Class.cv p)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0007 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((syn_cxpk B B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdminvalpex A B (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p dv_cache_0001 dv_cache_0003 dv_cache_0007 dv_cache_0005 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @g_fnmpti p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)) (syn_cfdpivmap2 R A B) dv_cache_0010 p0000 p0001
  exact p0002

noncomputable def g_fdpivrange2ex
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdpivrange2 R A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p_ne_z : p ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_p : z ≠ p :=
    Ne.symm fresh_p_ne_z
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint ((syn_cfdminsep R A B)).fv ((syn_csn (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint ((syn_cfdminsep R A B)).fv ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (((Class.cv z)).fv) from (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(show Disjoint ((A).fv) (((Class.cv z)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({z} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show z ∉ (A).fv from (by exact fresh_z_not_A)))))), (show Disjoint ((B).fv) (((Class.cv z)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({z} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show z ∉ (B).fv from (by exact fresh_z_not_B))))))⟩), (show Disjoint ((R).fv) (((Class.cv z)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((R).fv) (({z} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show z ∉ (R).fv from (by exact fresh_z_not_R))))))⟩))))
  have dv_cache_0008 : Disjoint ((syn_cfdminsep R A B)).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint ((syn_cfdminsep R A B)).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (({p} : Finset Var)) from (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact fresh_p_not_A)))), (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact fresh_p_not_B))))⟩), (show Disjoint ((R).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))⟩))))
  have dv_cache_0009 : Disjoint ((syn_csn (.cv z))).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint ((syn_csn (.cv z))).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (((Class.cv z)).fv) (({p} : Finset Var)) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({z} : Finset Var)) (({p} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show z ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ p from (by exact fresh_z_ne_p))))))))))
  have dv_cache_0010 : Disjoint (A).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint (A).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0011 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : Disjoint (B).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint (B).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0013 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : Disjoint ((Class.cv p)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show Disjoint ((Class.cv p)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0015 : z ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((syn_cxpk B B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_cfdminq R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_cfdminq R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((syn_cfdminvalp R A B (.cv p))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_p, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : p ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show p ≠ z from (by exact fresh_p_ne_z))
  have p0000 :=
    (by simpa [syn_cfdpivrange2] using (Nominal.classEqRefl (syn_cfdpivrange2 R A B)))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    (by simpa [syn_cfdminq] using (Nominal.classEqRefl (syn_cfdminq R A B)))
  have p0003 :=
    @g_eleq2i (syn_cfdminq R A B) (syn_ckqrel (syn_cfdminsep R A B)) (syn_cop (syn_csn (.cv z)) (.cv p)) p0002
  have p0004 :=
    @g_snex (.cv z)
  have p0005 :=
    @g_vex p
  have p0006 :=
    @g_kqrelbr (syn_cfdminsep R A B) (syn_csn (.cv z)) (.cv p) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0004 p0005
  have p0007 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_cfdminq R A B)) (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_ckqrel (syn_cfdminsep R A B))) (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) p0003 p0006
  have p0008 :=
    @g_vex p
  have p0009 :=
    @g_fdminvalpbr z A B (.cv p) R dv_cache_0001 dv_cache_0010 dv_cache_0002 dv_cache_0011 dv_cache_0012 dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 p0008
  have p0010 :=
    @g_bicomi (.classMem (.cv z) (syn_cfdminvalp R A B (.cv p))) (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) p0009
  have p0011 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_cfdminq R A B)) (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) (.classMem (.cv z) (syn_cfdminvalp R A B (.cv p))) p0007 p0010
  have p0012 :=
    @g_releqmpt p z (syn_cxpk B B) (syn_cfdminq R A B) (syn_cfdminvalp R A B (.cv p)) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0011
  have p0013 :=
    @g_eqtr4i (syn_cfdpivmap2 R A B) (syn_cmpt p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p))) (syn_cin (syn_cxp (syn_cxpk B B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdminq R A B))) (syn_c1c))))) p0001 p0012
  have p0014 :=
    @g_xpkex B B hyp_fdpivmap2ex_3 hyp_fdpivmap2ex_3
  have p0015 :=
    @g_fdminqex A B R hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0016 :=
    @g_mptexlem (syn_cxpk B B) (syn_cfdminq R A B) p0014 p0015
  have p0017 :=
    @g_eqeltri (syn_cfdpivmap2 R A B) (syn_cin (syn_cxp (syn_cxpk B B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdminq R A B))) (syn_c1c))))) (syn_cvv) p0013 p0016
  have p0018 :=
    @g_rnex (syn_cfdpivmap2 R A B) p0017
  have p0019 :=
    @g_eqeltri (syn_cfdpivrange2 R A B) (syn_crn (syn_cfdpivmap2 R A B)) (syn_cvv) p0000 p0018
  exact p0019

noncomputable def g_fdpivmap2onto
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv p)).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0005 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint ((Class.cv p)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint ((Class.cv p)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0007 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((syn_cxpk B B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdminvalpex A B (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p dv_cache_0001 dv_cache_0003 dv_cache_0007 dv_cache_0005 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @g_fnmpti p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)) (syn_cfdpivmap2 R A B) dv_cache_0010 p0000 p0001
  have p0003 :=
    @g_dffn4 (syn_cxpk B B) (syn_cfdpivmap2 R A B)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cfdpivmap2 R A B) (syn_cxpk B B)) (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_crn (syn_cfdpivmap2 R A B))) p0002 p0003
  have p0005 :=
    (by simpa [syn_cfdpivrange2] using (Nominal.classEqRefl (syn_cfdpivrange2 R A B)))
  have p0006 :=
    @g_eqcomi (syn_cfdpivrange2 R A B) (syn_crn (syn_cfdpivmap2 R A B)) p0005
  have p0007 :=
    @g_foeq3 (syn_crn (syn_cfdpivmap2 R A B)) (syn_cfdpivrange2 R A B) (syn_cxpk B B) (syn_cfdpivmap2 R A B)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbi (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_crn (syn_cfdpivmap2 R A B))) (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B)) p0004 p0008
  exact p0009

#print axioms g_fdpivmap2onto

end NFChoice.DirectNominalPrf.WPPReplay
