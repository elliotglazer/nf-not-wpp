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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk011Compact001Part006

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

noncomputable def g_rnuni
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_crn (syn_cuni A)) (syn_ciun x A (syn_crn (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have dv_cache_0001 : x ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.classMem (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cuni A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_crn (syn_cuni A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_ciun x A (syn_crn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eluni x (syn_cop (.cv y) (.cv z)) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_exbii (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A)) (syn_wex x (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))) y p0000
  have p0002 :=
    @g_excom (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)) y x
  have p0003 :=
    @g_elrn2 y (.cv z) (.cv x) dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_anbi1i (.classMem (.cv z) (syn_crn (.cv x))) (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A) p0003
  have p0005 :=
    @g_ancom (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x)))
  have p0006 :=
    @g_n_19_41v (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A) y dv_cache_0005
  have p0007 :=
    @g_n_3bitr4ri (syn_wa (.classMem (.cv z) (syn_crn (.cv x))) (.classMem (.cv x) A)) (syn_wa (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x)))) (syn_wex y (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))) p0004 p0005 p0006
  have p0008 :=
    @g_exbii (syn_wex y (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x)))) x p0007
  have p0009 :=
    @g_n_3bitri (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A))) (syn_wex y (syn_wex x (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))) (syn_wex x (syn_wex y (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x))))) p0001 p0002 p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x A (.classMem (.cv z) (syn_crn (.cv x))))))
  have p0011 :=
    @g_bitr4i (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A))) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x))))) (syn_wrex x A (.classMem (.cv z) (syn_crn (.cv x)))) p0009 p0010
  have p0012 :=
    @g_elrn2 y (.cv z) (syn_cuni A) dv_cache_0003 dv_cache_0006
  have p0013 :=
    @g_eliun x (.cv z) A (syn_crn (.cv x)) dv_cache_0007
  have p0014 :=
    @g_n_3bitr4i (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A))) (syn_wrex x A (.classMem (.cv z) (syn_crn (.cv x)))) (.classMem (.cv z) (syn_crn (syn_cuni A))) (.classMem (.cv z) (syn_ciun x A (syn_crn (.cv x)))) p0011 p0012 p0013
  have p0015 :=
    @g_eqriv z (syn_crn (syn_cuni A)) (syn_ciun x A (syn_crn (.cv x))) dv_cache_0008 dv_cache_0009 p0014
  exact p0015

noncomputable def g_imaundi
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cima A (syn_cun B C)) (syn_cun (syn_cima A B) (syn_cima A C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_resundi A B C
  have p0001 :=
    @g_rneqi (syn_cres A (syn_cun B C)) (syn_cun (syn_cres A B) (syn_cres A C)) p0000
  have p0002 :=
    @g_rnun (syn_cres A B) (syn_cres A C)
  have p0003 :=
    @g_eqtri (syn_crn (syn_cres A (syn_cun B C))) (syn_crn (syn_cun (syn_cres A B) (syn_cres A C))) (syn_cun (syn_crn (syn_cres A B)) (syn_crn (syn_cres A C))) p0001 p0002
  have p0004 :=
    @g_dfima3 A (syn_cun B C)
  have p0005 :=
    @g_dfima3 A B
  have p0006 :=
    @g_dfima3 A C
  have p0007 :=
    @g_uneq12i (syn_cima A B) (syn_crn (syn_cres A B)) (syn_cima A C) (syn_crn (syn_cres A C)) p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_crn (syn_cres A (syn_cun B C))) (syn_cun (syn_crn (syn_cres A B)) (syn_crn (syn_cres A C))) (syn_cima A (syn_cun B C)) (syn_cun (syn_cima A B) (syn_cima A C)) p0003 p0004 p0007
  exact p0008

noncomputable def g_imaundir
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cima (syn_cun A B) C) (syn_cun (syn_cima A C) (syn_cima B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_dfima3 (syn_cun A B) C
  have p0001 :=
    @g_resundir A B C
  have p0002 :=
    @g_rneqi (syn_cres (syn_cun A B) C) (syn_cun (syn_cres A C) (syn_cres B C)) p0001
  have p0003 :=
    @g_rnun (syn_cres A C) (syn_cres B C)
  have p0004 :=
    @g_n_3eqtri (syn_cima (syn_cun A B) C) (syn_crn (syn_cres (syn_cun A B) C)) (syn_crn (syn_cun (syn_cres A C) (syn_cres B C))) (syn_cun (syn_crn (syn_cres A C)) (syn_crn (syn_cres B C))) p0000 p0002 p0003
  have p0005 :=
    @g_dfima3 A C
  have p0006 :=
    @g_dfima3 B C
  have p0007 :=
    @g_uneq12i (syn_cima A C) (syn_crn (syn_cres A C)) (syn_cima B C) (syn_crn (syn_cres B C)) p0005 p0006
  have p0008 :=
    @g_eqtr4i (syn_cima (syn_cun A B) C) (syn_cun (syn_crn (syn_cres A C)) (syn_crn (syn_cres B C))) (syn_cun (syn_cima A C) (syn_cima B C)) p0004 p0007
  exact p0008

noncomputable def g_cnvxp
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cxp A B)) (syn_cxp B A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ≠ x := by
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_cnvopab (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)) y x dv_cache_0001
  have p0001 :=
    @g_ancom (.classMem (.cv y) A) (.classMem (.cv x) B)
  have p0002 :=
    @g_opabbii (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) A)) x y p0001
  have p0003 :=
    @g_eqtri (syn_ccnv (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)))) (syn_copab x y (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B))) (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) A))) p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp y x A B dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0001
  have p0005 :=
    @g_cnveqi (syn_cxp A B) (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B))) p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y B A dv_cache_0005 dv_cache_0004 dv_cache_0003 dv_cache_0002 dv_cache_0006
  have p0007 :=
    @g_n_3eqtr4i (syn_ccnv (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)))) (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) A))) (syn_ccnv (syn_cxp A B)) (syn_cxp B A) p0003 p0005 p0006
  exact p0007

noncomputable def g_xp0
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cxp A (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_xp0r A
  have p0001 :=
    @g_cnveqi (syn_cxp (syn_c0) A) (syn_c0) p0000
  have p0002 :=
    @g_cnvxp (syn_c0) A
  have p0003 :=
    @g_cnv0
  have p0004 :=
    @g_n_3eqtr3i (syn_ccnv (syn_cxp (syn_c0) A)) (syn_ccnv (syn_c0)) (syn_cxp A (syn_c0)) (syn_c0) p0001 p0002 p0003
  exact p0004

noncomputable def g_xpdisj2
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cin (syn_cxp C A) (syn_cxp D B)) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_inxp C A D B
  have p0001 :=
    @g_xpeq2 (syn_cin A B) (syn_c0) (syn_cin C D)
  have p0002 :=
    @g_xp0 (syn_cin C D)
  have p0003 :=
    @g_syl6eq (.classEq (syn_cin A B) (syn_c0)) (syn_cxp (syn_cin C D) (syn_cin A B)) (syn_cxp (syn_cin C D) (syn_c0)) (syn_c0) p0001 p0002
  have p0004 :=
    @g_syl5eq (.classEq (syn_cin A B) (syn_c0)) (syn_cin (syn_cxp C A) (syn_cxp D B)) (syn_cxp (syn_cin C D) (syn_cin A B)) (syn_c0) p0000 p0003
  exact p0004

noncomputable def g_dmxpss
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cdm (syn_cxp A B)) A) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_n_0ss A
  have p0001 :=
    @g_xpeq2 B (syn_c0) A
  have p0002 :=
    @g_xp0 A
  have p0003 :=
    @g_syl6eq (.classEq B (syn_c0)) (syn_cxp A B) (syn_cxp A (syn_c0)) (syn_c0) p0001 p0002
  have p0004 :=
    @g_dmeqd (.classEq B (syn_c0)) (syn_cxp A B) (syn_c0) p0003
  have p0005 :=
    @g_dm0
  have p0006 :=
    @g_syl6eq (.classEq B (syn_c0)) (syn_cdm (syn_cxp A B)) (syn_cdm (syn_c0)) (syn_c0) p0004 p0005
  have p0007 :=
    @g_sseq1d (.classEq B (syn_c0)) (syn_cdm (syn_cxp A B)) (syn_c0) A p0006
  have p0008 :=
    @g_mpbiri (.classEq B (syn_c0)) (syn_wss (syn_cdm (syn_cxp A B)) A) (syn_wss (syn_c0) A) p0000 p0007
  have p0009 :=
    @g_dmxp A B
  have p0010 :=
    @g_eqimss (syn_cdm (syn_cxp A B)) A
  have p0011 :=
    @g_syl (syn_wne B (syn_c0)) (.classEq (syn_cdm (syn_cxp A B)) A) (syn_wss (syn_cdm (syn_cxp A B)) A) p0009 p0010
  have p0012 :=
    @g_pm2_61ine (syn_wss (syn_cdm (syn_cxp A B)) A) B (syn_c0) p0008 p0011
  exact p0012

noncomputable def g_rnxpss
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_crn (syn_cxp A B)) B) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dfrn4 (syn_cxp A B)
  have p0001 :=
    @g_cnvxp A B
  have p0002 :=
    @g_dmeqi (syn_ccnv (syn_cxp A B)) (syn_cxp B A) p0001
  have p0003 :=
    @g_eqtri (syn_crn (syn_cxp A B)) (syn_cdm (syn_ccnv (syn_cxp A B))) (syn_cdm (syn_cxp B A)) p0000 p0002
  have p0004 :=
    @g_dmxpss B A
  have p0005 :=
    @g_eqsstri (syn_crn (syn_cxp A B)) (syn_cdm (syn_cxp B A)) B p0003 p0004
  exact p0005

noncomputable def g_cnvcnv
    (R : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_ccnv R)) R) := by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_ccnv R))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_ccnv R))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_brcnv (.cv x) (.cv y) (syn_ccnv R)
  have p0001 :=
    @g_brcnv (.cv y) (.cv x) R
  have p0002 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_ccnv R)) (.cv y)) (syn_wbr (.cv y) (syn_ccnv R) (.cv x)) (syn_wbr (.cv x) R (.cv y)) p0000 p0001
  have p0003 :=
    @g_eqbrriv x y (syn_ccnv (syn_ccnv R)) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0002
  exact p0003

noncomputable def g_cnveqb
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq A B) (.classEq (syn_ccnv A) (syn_ccnv B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_cnveq A B
  have p0001 :=
    @g_cnveq (syn_ccnv A) (syn_ccnv B)
  have p0002 :=
    @g_cnvcnv A
  have p0003 :=
    @g_cnvcnv B
  have p0004 :=
    @g_n_3eqtr3g (.classEq (syn_ccnv A) (syn_ccnv B)) (syn_ccnv (syn_ccnv A)) (syn_ccnv (syn_ccnv B)) A B p0001 p0002 p0003
  have p0005 :=
    @g_impbii (.classEq A B) (.classEq (syn_ccnv A) (syn_ccnv B)) p0000 p0004
  exact p0005

noncomputable def g_dmsnopg
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classEq (.cv x) A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_csn (syn_cop A (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cdm (syn_csn (syn_cop A (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_csn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_opeq2 (.cv y) B A
  have p0001 :=
    @g_sneqd (.classEq (.cv y) B) (syn_cop A (.cv y)) (syn_cop A B) p0000
  have p0002 :=
    @g_dmeqd (.classEq (.cv y) B) (syn_csn (syn_cop A (.cv y))) (syn_csn (syn_cop A B)) p0001
  have p0003 :=
    @g_eqeq1d (.classEq (.cv y) B) (syn_cdm (syn_csn (syn_cop A (.cv y)))) (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A) p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z))))
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_opex (.cv x) (.cv z) p0005 p0006
  have p0008 :=
    @g_elsnc (syn_cop (.cv x) (.cv z)) (syn_cop A (.cv y)) p0007
  have p0009 :=
    @g_opth (.cv x) (.cv z) A (.cv y)
  have p0010 :=
    @g_ancom (.classEq (.cv x) A) (.objEq z y)
  have p0011_e00_recanon : Nominal.NPrf (syn_wb (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop A (.cv y))) (syn_wa (.classEq (.cv x) A) (.objEq z y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0011 :=
    @g_bitri (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop A (.cv y))) (syn_wa (.classEq (.cv x) A) (.objEq z y)) (syn_wa (.objEq z y) (.classEq (.cv x) A)) p0011_e00_recanon p0010
  have p0012 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_csn (syn_cop A (.cv y)))) (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop A (.cv y))) (syn_wa (.objEq z y) (.classEq (.cv x) A)) p0004 p0008 p0011
  have p0013 :=
    @g_exbii (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z)) (syn_wa (.objEq z y) (.classEq (.cv x) A)) z p0012
  have p0014 :=
    @g_vex y
  have p0015 :=
    @g_biidd (.objEq z y) (.classEq (.cv x) A)
  have p0016_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv z) (.cv y)) (syn_wb (.classEq (.cv x) A) (.classEq (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0015
  have p0016 :=
    @g_ceqsexv (.classEq (.cv x) A) (.classEq (.cv x) A) z (.cv y) dv_cache_0001 dv_cache_0002 p0014 p0016_e01_recanon
  have p0017_e01_recanon : Nominal.NPrf (syn_wb (syn_wex z (syn_wa (.objEq z y) (.classEq (.cv x) A))) (.classEq (.cv x) A)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0017 :=
    @g_bitri (syn_wex z (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z))) (syn_wex z (syn_wa (.objEq z y) (.classEq (.cv x) A))) (.classEq (.cv x) A) p0013 p0017_e01_recanon
  have p0018 :=
    @g_eldm z (.cv x) (syn_csn (syn_cop A (.cv y))) dv_cache_0003 dv_cache_0004
  have p0019 :=
    @g_elsn x A dv_cache_0005
  have p0020 :=
    @g_n_3bitr4i (syn_wex z (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z))) (.classEq (.cv x) A) (.classMem (.cv x) (syn_cdm (syn_csn (syn_cop A (.cv y))))) (.classMem (.cv x) (syn_csn A)) p0017 p0018 p0019
  have p0021 :=
    @g_eqriv x (syn_cdm (syn_csn (syn_cop A (.cv y)))) (syn_csn A) dv_cache_0006 dv_cache_0007 p0020
  have p0022 :=
    @g_vtoclg (.classEq (syn_cdm (syn_csn (syn_cop A (.cv y)))) (syn_csn A)) (.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A)) y B V dv_cache_0008 dv_cache_0009 p0003 p0021
  exact p0022

noncomputable def g_dmsnop
    (A : Class) (B : Class) (hyp_dmsnop_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dmsnopg A B (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_dmsnop_1 p0000
  exact p0001

noncomputable def g_cnvsn
    (A : Class) (B : Class) (hyp_cnvsn_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_cnvsn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn (syn_cop B A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_csn (syn_cop A B)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_csn (syn_cop A B)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_csn (syn_cop B A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_csn (syn_cop B A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_vex y
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_opex (.cv y) (.cv x) p0000 p0001
  have p0003 :=
    @g_elsnc (syn_cop (.cv y) (.cv x)) (syn_cop A B) p0002
  have p0004 :=
    @g_ancom (.classEq (.cv y) A) (.classEq (.cv x) B)
  have p0005 :=
    @g_opth (.cv y) (.cv x) A B
  have p0006 :=
    @g_opth (.cv x) (.cv y) B A
  have p0007 :=
    @g_n_3bitr4i (syn_wa (.classEq (.cv y) A) (.classEq (.cv x) B)) (syn_wa (.classEq (.cv x) B) (.classEq (.cv y) A)) (.classEq (syn_cop (.cv y) (.cv x)) (syn_cop A B)) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B A)) p0004 p0005 p0006
  have p0008 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv x)) (syn_csn (syn_cop A B))) (.classEq (syn_cop (.cv y) (.cv x)) (syn_cop A B)) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B A)) p0003 p0007
  have p0009 :=
    @g_opelcnv (.cv x) (.cv y) (syn_csn (syn_cop A B))
  have p0010 :=
    @g_opex (.cv x) (.cv y) p0001 p0000
  have p0011 :=
    @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop B A) p0010
  have p0012 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv y) (.cv x)) (syn_csn (syn_cop A B))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B A)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv (syn_csn (syn_cop A B)))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop B A))) p0008 p0009 p0011
  have p0013 :=
    @g_eqrelriv x y (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn (syn_cop B A)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0012
  exact p0013

noncomputable def g_rnsnop
    (A : Class) (B : Class) (hyp_rnsnop_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_crn (syn_csn (syn_cop A B))) (syn_csn B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_csn (syn_cop A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_crn (syn_csn (syn_cop A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_csn B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))))
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_vex y
  have p0003 :=
    @g_opex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop A B) p0003
  have p0005 :=
    @g_opth (.cv x) (.cv y) A B
  have p0006 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B)) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0004 p0005
  have p0007 :=
    @g_bitri (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B))) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0000 p0006
  have p0008 :=
    @g_exbii (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) x p0007
  have p0009 :=
    @g_biidd (.classEq (.cv x) A) (.classEq (.cv y) B)
  have p0010 :=
    @g_ceqsexv (.classEq (.cv y) B) (.classEq (.cv y) B) x A dv_cache_0001 dv_cache_0002 hyp_rnsnop_1 p0009
  have p0011 :=
    @g_bitri (syn_wex x (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))) (syn_wex x (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))) (.classEq (.cv y) B) p0008 p0010
  have p0012 :=
    @g_elrn x (.cv y) (syn_csn (syn_cop A B)) dv_cache_0003 dv_cache_0004
  have p0013 :=
    @g_elsnc (.cv y) B p0002
  have p0014 :=
    @g_n_3bitr4i (syn_wex x (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))) (.classEq (.cv y) B) (.classMem (.cv y) (syn_crn (syn_csn (syn_cop A B)))) (.classMem (.cv y) (syn_csn B)) p0011 p0012 p0013
  have p0015 :=
    @g_eqriv y (syn_crn (syn_csn (syn_cop A B))) (syn_csn B) dv_cache_0005 dv_cache_0006 p0014
  exact p0015

noncomputable def g_cnvresima
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.classEq (syn_cima (syn_ccnv (syn_cres F A)) B) (syn_cin (syn_cima (syn_ccnv F) B) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let t : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_F : t ∉ F.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_not_F : s ∉ F.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_t_ne_s : t ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_t : s ≠ t :=
    Ne.symm fresh_t_ne_s
  have dv_cache_0001 : s ∉ ((Class.cv t)).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : s ∉ ((syn_ccnv (syn_cres F A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_F, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : s ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((Wff.classMem (.cv t) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_t, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : s ∉ ((syn_ccnv F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_cima (syn_ccnv (syn_cres F A)) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_F, fresh_t_not_A, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_cin (syn_cima (syn_ccnv F) B) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_F, fresh_t_not_B, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elima3 s (.cv t) (syn_ccnv (syn_cres F A)) B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_anass (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)) (.classMem (.cv t) A)
  have p0002 :=
    @g_opelres (.cv t) (.cv s) F A
  have p0003 :=
    @g_opelcnv (.cv s) (.cv t) (syn_cres F A)
  have p0004 :=
    @g_opelcnv (.cv s) (.cv t) F
  have p0005 :=
    @g_anbi1i (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)) (.classMem (syn_cop (.cv t) (.cv s)) F) (.classMem (.cv t) A) p0004
  have p0006 :=
    @g_n_3bitr4ri (.classMem (syn_cop (.cv t) (.cv s)) (syn_cres F A)) (syn_wa (.classMem (syn_cop (.cv t) (.cv s)) F) (.classMem (.cv t) A)) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A))) (syn_wa (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)) (.classMem (.cv t) A)) p0002 p0003 p0005
  have p0007 :=
    @g_anbi2i (syn_wa (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)) (.classMem (.cv t) A)) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A))) (.classMem (.cv s) B) p0006
  have p0008 :=
    @g_bitr2i (syn_wa (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F))) (.classMem (.cv t) A)) (syn_wa (.classMem (.cv s) B) (syn_wa (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)) (.classMem (.cv t) A))) (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A)))) p0001 p0007
  have p0009 :=
    @g_exbii (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A)))) (syn_wa (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F))) (.classMem (.cv t) A)) s p0008
  have p0010 :=
    @g_n_19_41v (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F))) (.classMem (.cv t) A) s dv_cache_0004
  have p0011 :=
    @g_bitri (syn_wex s (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A))))) (syn_wex s (syn_wa (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F))) (.classMem (.cv t) A))) (syn_wa (syn_wex s (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))) (.classMem (.cv t) A)) p0009 p0010
  have p0012 :=
    @g_elin (.cv t) (syn_cima (syn_ccnv F) B) A
  have p0013 :=
    @g_elima3 s (.cv t) (syn_ccnv F) B dv_cache_0001 dv_cache_0005 dv_cache_0003
  have p0014 :=
    @g_anbi1i (.classMem (.cv t) (syn_cima (syn_ccnv F) B)) (syn_wex s (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))) (.classMem (.cv t) A) p0013
  have p0015 :=
    @g_bitr2i (.classMem (.cv t) (syn_cin (syn_cima (syn_ccnv F) B) A)) (syn_wa (.classMem (.cv t) (syn_cima (syn_ccnv F) B)) (.classMem (.cv t) A)) (syn_wa (syn_wex s (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))) (.classMem (.cv t) A)) p0012 p0014
  have p0016 :=
    @g_n_3bitri (.classMem (.cv t) (syn_cima (syn_ccnv (syn_cres F A)) B)) (syn_wex s (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A))))) (syn_wa (syn_wex s (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))) (.classMem (.cv t) A)) (.classMem (.cv t) (syn_cin (syn_cima (syn_ccnv F) B) A)) p0000 p0011 p0015
  have p0017 :=
    @g_eqriv t (syn_cima (syn_ccnv (syn_cres F A)) B) (syn_cin (syn_cima (syn_ccnv F) B) A) dv_cache_0006 dv_cache_0007 p0016
  exact p0017

#print axioms g_cnvresima

end NFChoice.DirectNominalPrf.WPPReplay
