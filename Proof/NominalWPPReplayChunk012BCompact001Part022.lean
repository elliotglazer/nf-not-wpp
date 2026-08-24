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
import NominalWPPReplayChunk012BCompact001Part021

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

noncomputable def g_otelins3
    (A : Class) (B : Class) (C : Class) (R : Class) (hyp_otelins3_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R)) (.classMem (syn_cop A B) R)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (syn_cop A B) R)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex (syn_cop A (syn_cop B C)) (syn_cins3 R)
  have p0001 :=
    @g_opexb A (syn_cop B C)
  have p0002 :=
    @g_simplbi (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem (syn_cop B C) (syn_cvv)) p0001
  have p0003 :=
    @g_syl (.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R)) (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (.classMem A (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_elex (syn_cop A B) R
  have p0005 :=
    @g_opexb A B
  have p0006 :=
    @g_simplbi (.classMem (syn_cop A B) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0005
  have p0007 :=
    @g_syl (.classMem (syn_cop A B) R) (.classMem (syn_cop A B) (syn_cvv)) (.classMem A (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_opeq1 (.cv x) A (syn_cop B C)
  have p0009 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cop B C)) (syn_cop A (syn_cop B C)) (syn_cins3 R) p0008
  have p0010 :=
    @g_opeq1 (.cv x) A B
  have p0011 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) B) (syn_cop A B) R p0010
  have p0012 :=
    @g_vex x
  have p0013 :=
    @g_opex (.cv x) C p0012 hyp_otelins3_1
  have p0014 :=
    (by simpa [syn_cins3] using (Nominal.classEqRefl (syn_cins3 R)))
  have p0015 :=
    @g_eleq2i (syn_cins3 R) (syn_ctxp R (syn_cvv)) (syn_cop (.cv x) (syn_cop B C)) p0014
  have p0016 :=
    @g_oteltxp (.cv x) B C R (syn_cvv)
  have p0017 :=
    @g_bitri (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins3 R)) (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_ctxp R (syn_cvv))) (syn_wa (.classMem (syn_cop (.cv x) B) R) (.classMem (syn_cop (.cv x) C) (syn_cvv))) p0015 p0016
  have p0018 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins3 R)) (.classMem (syn_cop (.cv x) B) R) (.classMem (syn_cop (.cv x) C) (syn_cvv)) p0013 p0017
  have p0019 :=
    @g_vtoclbg (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins3 R)) (.classMem (syn_cop (.cv x) B) R) (.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R)) (.classMem (syn_cop A B) R) x A (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0009 p0011 p0018
  have p0020 :=
    @g_pm5_21nii (.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R)) (.classMem A (syn_cvv)) (.classMem (syn_cop A B) R) p0003 p0007 p0019
  exact p0020

noncomputable def g_brimage
    (A : Class) (B : Class) (R : Class) (hyp_brimage_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_brimage_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cimage R) B) (.classEq B (syn_cima R A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_R : t ∉ R.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_t_ne_y : t ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have dv_cache_0001 : x ∉ ((syn_cop A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wbr (.cv t) (syn_csset) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_csn (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_not_A, fresh_t_ne_x, fresh_t_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((syn_csset)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : t ∉ ((syn_ccnv (syn_csi R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cima R A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elima1c x (syn_cop A B) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elsymdif (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))
  have p0002 :=
    @g_otelins2 (syn_csn (.cv x)) A B (syn_csset) hyp_brimage_1
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_opelssetsn (.cv x) B p0003 hyp_brimage_2
  have p0005 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv x)) B) (syn_csset)) (.classMem (.cv x) B) p0002 p0004
  have p0006 :=
    @g_otelins3 (syn_csn (.cv x)) A B (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))) hyp_brimage_2
  have p0007 :=
    @g_brcnv (syn_csn (.cv x)) (.cv t) (syn_csi R)
  have p0008 :=
    @g_brsnsi2 y (.cv x) (.cv t) R dv_cache_0003 dv_cache_0004 dv_cache_0005 p0003
  have p0009 :=
    @g_bitri (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t)) (syn_wbr (.cv t) (syn_csi R) (syn_csn (.cv x))) (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))) p0007 p0008
  have p0010 :=
    @g_anbi1i (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t)) (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))) (syn_wbr (.cv t) (syn_csset) A) p0009
  have p0011 :=
    @g_n_19_41v (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv t) (syn_csset) A) y dv_cache_0006
  have p0012 :=
    @g_bitr4i (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t)) (syn_wbr (.cv t) (syn_csset) A)) (syn_wa (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))) (syn_wbr (.cv t) (syn_csset) A)) (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv t) (syn_csset) A))) p0010 p0011
  have p0013 :=
    @g_exbii (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t)) (syn_wbr (.cv t) (syn_csset) A)) (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv t) (syn_csset) A))) t p0012
  have p0014 :=
    @g_excom (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv t) (syn_csset) A)) t y
  have p0015 :=
    @g_anass (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv t) (syn_csset) A)
  have p0016 :=
    @g_exbii (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv t) (syn_csset) A)) (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv t) (syn_csset) A))) t p0015
  have p0017 :=
    @g_snex (.cv y)
  have p0018 :=
    @g_breq1 (.cv t) (syn_csn (.cv y)) A (syn_csset)
  have p0019 :=
    @g_anbi2d (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv t) (syn_csset) A) (syn_wbr (syn_csn (.cv y)) (syn_csset) A) (syn_wbr (.cv y) R (.cv x)) p0018
  have p0020 :=
    @g_ancom (syn_wbr (.cv y) R (.cv x)) (syn_wbr (syn_csn (.cv y)) (syn_csset) A)
  have p0021 :=
    @g_vex y
  have p0022 :=
    @g_brssetsn (.cv y) A p0021 hyp_brimage_1
  have p0023 :=
    @g_anbi1i (syn_wbr (syn_csn (.cv y)) (syn_csset) A) (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x)) p0022
  have p0024 :=
    @g_bitri (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (syn_csn (.cv y)) (syn_csset) A)) (syn_wa (syn_wbr (syn_csn (.cv y)) (syn_csset) A) (syn_wbr (.cv y) R (.cv x))) (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) p0020 p0023
  have p0025 :=
    @g_syl6bb (.classEq (.cv t) (syn_csn (.cv y))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv t) (syn_csset) A)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (syn_csn (.cv y)) (syn_csset) A)) (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) p0019 p0024
  have p0026 :=
    @g_ceqsexv (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv t) (syn_csset) A)) (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) t (syn_csn (.cv y)) dv_cache_0007 dv_cache_0008 p0017 p0025
  have p0027 :=
    @g_bitri (syn_wex t (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv t) (syn_csset) A))) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv t) (syn_csset) A)))) (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) p0016 p0026
  have p0028 :=
    @g_exbii (syn_wex t (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv t) (syn_csset) A))) (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) y p0027
  have p0029 :=
    @g_n_3bitri (syn_wex t (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t)) (syn_wbr (.cv t) (syn_csset) A))) (syn_wex t (syn_wex y (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv t) (syn_csset) A)))) (syn_wex y (syn_wex t (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv t) (syn_csset) A)))) (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x)))) p0013 p0014 p0028
  have p0030 :=
    @g_opelco t (syn_csn (.cv x)) A (syn_csset) (syn_ccnv (syn_csi R)) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0031 :=
    @g_elima2 y (.cv x) R A dv_cache_0003 dv_cache_0005 dv_cache_0013
  have p0032 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t)) (syn_wbr (.cv t) (syn_csset) A))) (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x)))) (.classMem (syn_cop (syn_csn (.cv x)) A) (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))) (.classMem (.cv x) (syn_cima R A)) p0029 p0030 p0031
  have p0033 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (.classMem (syn_cop (syn_csn (.cv x)) A) (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))) (.classMem (.cv x) (syn_cima R A)) p0006 p0032
  have p0034 :=
    @g_bibi12i (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins2 (syn_csset))) (.classMem (.cv x) B) (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (.classMem (.cv x) (syn_cima R A)) p0005 p0033
  have p0035 :=
    @g_xchbinx (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))))) (syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))))) (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A))) p0001 p0034
  have p0036 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))))) (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A)))) x p0035
  have p0037 :=
    @g_exnal (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A))) x
  have p0038 :=
    @g_n_3bitri (.classMem (syn_cop A B) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))) (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))))) (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A))))) (.neg (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A))))) p0000 p0036 p0037
  have p0039 :=
    @g_con2bii (.classMem (syn_cop A B) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))) (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A)))) p0038
  have p0040 :=
    @g_dfcleq x B (syn_cima R A) dv_cache_0014 dv_cache_0015
  have p0041 :=
    (by simpa [syn_cimage] using (Nominal.classEqRefl (syn_cimage R)))
  have p0042 :=
    @g_breqi A B (syn_cimage R) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))) p0041
  have p0043 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))) B)))
  have p0044 :=
    @g_opex A B hyp_brimage_1 hyp_brimage_2
  have p0045 :=
    @g_elcompl (syn_cop A B) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c)) p0044
  have p0046 :=
    @g_n_3bitri (syn_wbr A (syn_cimage R) B) (syn_wbr A (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))) B) (.classMem (syn_cop A B) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c)))) (.neg (.classMem (syn_cop A B) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c)))) p0042 p0043 p0045
  have p0047 :=
    @g_n_3bitr4ri (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A)))) (.neg (.classMem (syn_cop A B) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c)))) (.classEq B (syn_cima R A)) (syn_wbr A (syn_cimage R) B) p0039 p0040 p0046
  exact p0047

#print axioms g_brimage

end NFChoice.DirectNominalPrf.WPPReplay
