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
import NominalWPPReplayChunk011Compact001Part002

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

noncomputable def g_dmuni
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cuni A)) (syn_ciun x A (syn_cdm (.cv x)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
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
  have dv_cache_0003 : z ∉ ((Wff.classMem (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cuni A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cdm (syn_cuni A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_ciun x A (syn_cdm (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eluni x (syn_cop (.cv y) (.cv z)) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_exbii (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A)) (syn_wex x (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))) z p0000
  have p0002 :=
    @g_excom (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)) z x
  have p0003 :=
    @g_n_19_41v (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A) z dv_cache_0003
  have p0004 :=
    @g_ancom (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))
  have p0005 :=
    @g_eldm2 z (.cv y) (.cv x) dv_cache_0004 dv_cache_0005
  have p0006 :=
    @g_anbi1i (.classMem (.cv y) (syn_cdm (.cv x))) (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A) p0005
  have p0007 :=
    @g_bitri (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))) (syn_wa (.classMem (.cv y) (syn_cdm (.cv x))) (.classMem (.cv x) A)) (syn_wa (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A)) p0004 p0006
  have p0008 :=
    @g_bicomi (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))) (syn_wa (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A)) p0007
  have p0009 :=
    @g_bitri (syn_wex z (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))) (syn_wa (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))) p0003 p0008
  have p0010 :=
    @g_exbii (syn_wex z (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))) x p0009
  have p0011 :=
    @g_n_3bitri (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A))) (syn_wex z (syn_wex x (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))) (syn_wex x (syn_wex z (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x))))) p0001 p0002 p0010
  have p0012 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x A (.classMem (.cv y) (syn_cdm (.cv x))))))
  have p0013 :=
    @g_bitr4i (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A))) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x))))) (syn_wrex x A (.classMem (.cv y) (syn_cdm (.cv x)))) p0011 p0012
  have p0014 :=
    @g_eldm2 z (.cv y) (syn_cuni A) dv_cache_0004 dv_cache_0006
  have p0015 :=
    @g_eliun x (.cv y) A (syn_cdm (.cv x)) dv_cache_0007
  have p0016 :=
    @g_n_3bitr4i (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A))) (syn_wrex x A (.classMem (.cv y) (syn_cdm (.cv x)))) (.classMem (.cv y) (syn_cdm (syn_cuni A))) (.classMem (.cv y) (syn_ciun x A (syn_cdm (.cv x)))) p0013 p0014 p0015
  have p0017 :=
    @g_eqriv y (syn_cdm (syn_cuni A)) (syn_ciun x A (syn_cdm (.cv x))) dv_cache_0008 dv_cache_0009 p0016
  exact p0017

noncomputable def g_dmopab
    (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cdm (syn_copab x y ph)) (.cab x (syn_wex y ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_nfopab1 ph x y
  have p0001 :=
    @g_nfopab2 ph x y
  have p0002 :=
    @g_dfdmf x y (syn_copab x y ph) dv_cache_0001 p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))))
  have p0004 :=
    @g_opabid ph x y
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab x y ph)) ph p0003 p0004
  have p0006 :=
    @g_exbii (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)) ph y p0005
  have p0007 :=
    @g_abbii (syn_wex y (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))) (syn_wex y ph) x p0006
  have p0008 :=
    @g_eqtri (syn_cdm (syn_copab x y ph)) (.cab x (syn_wex y (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)))) (.cab x (syn_wex y ph)) p0002 p0007
  exact p0008

noncomputable def g_dmopab3
    (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wral x A (syn_wex y ph)) (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0002 : y ∉ ((Wff.classMem (.cv x) A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x A (syn_wex y ph))))
  have p0001 :=
    @g_pm4_71 (.classMem (.cv x) A) (syn_wex y ph)
  have p0002 :=
    @g_albii (.imp (.classMem (.cv x) A) (syn_wex y ph)) (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (syn_wex y ph))) x p0001
  have p0003 :=
    @g_dmopab (syn_wa (.classMem (.cv x) A) ph) x y dv_cache_0001
  have p0004 :=
    @g_n_19_42v (.classMem (.cv x) A) ph y dv_cache_0002
  have p0005 :=
    @g_abbii (syn_wex y (syn_wa (.classMem (.cv x) A) ph)) (syn_wa (.classMem (.cv x) A) (syn_wex y ph)) x p0004
  have p0006 :=
    @g_eqtri (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) (.cab x (syn_wex y (syn_wa (.classMem (.cv x) A) ph))) (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph))) p0003 p0005
  have p0007 :=
    @g_eqeq1i (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph))) A p0006
  have p0008 :=
    @g_eqcom A (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph)))
  have p0009 :=
    @g_eqabb (syn_wa (.classMem (.cv x) A) (syn_wex y ph)) x A dv_cache_0003
  have p0010 :=
    @g_n_3bitr2ri (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A) (.classEq (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph))) A) (.classEq A (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph)))) (.all x (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (syn_wex y ph)))) p0007 p0008 p0009
  have p0011 :=
    @g_n_3bitri (syn_wral x A (syn_wex y ph)) (.all x (.imp (.classMem (.cv x) A) (syn_wex y ph))) (.all x (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (syn_wex y ph)))) (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A) p0000 p0002 p0010
  exact p0011

noncomputable def g_dm0
     :
    Nominal.NPrf (.classEq (syn_cdm (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_cdm (syn_c0))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eq0 x (syn_cdm (syn_c0)) dv_cache_0001
  have p0001 :=
    @g_noel (syn_cop (.cv x) (.cv y))
  have p0002 :=
    @g_nex (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0)) y p0001
  have p0003 :=
    @g_eldm2 y (.cv x) (syn_c0) dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_mtbir (.classMem (.cv x) (syn_cdm (syn_c0))) (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0))) p0002 p0003
  have p0005 :=
    @g_mpgbir (.classEq (syn_cdm (syn_c0)) (syn_c0)) (.neg (.classMem (.cv x) (syn_cdm (syn_c0)))) x p0000 p0004
  exact p0005

noncomputable def g_dmi
     :
    Nominal.NPrf (.classEq (syn_cdm (syn_cid)) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_cdm (syn_cid))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cid)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqv x (syn_cdm (syn_cid)) dv_cache_0001
  have p0001 :=
    @g_a9e y x
  have p0002 :=
    @g_vex y
  have p0003 :=
    @g_ideq (.cv x) (.cv y) p0002
  have p0004 :=
    @g_equcom x y
  have p0005_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cid syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y) (.objEq y x) p0005_e00_recanon p0004
  have p0006 :=
    @g_exbii (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq y x) y p0005
  have p0007 :=
    @g_mpbir (syn_wex y (syn_wbr (.cv x) (syn_cid) (.cv y))) (syn_wex y (.objEq y x)) p0001 p0006
  have p0008 :=
    @g_eldm y (.cv x) (syn_cid) dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_mpbir (.classMem (.cv x) (syn_cdm (syn_cid))) (syn_wex y (syn_wbr (.cv x) (syn_cid) (.cv y))) p0007 p0008
  have p0010 :=
    @g_mpgbir (.classEq (syn_cdm (syn_cid)) (syn_cvv)) (.classMem (.cv x) (syn_cdm (syn_cid))) x p0000 p0009
  exact p0010

noncomputable def g_dm0rn0
    (A : Class) :
    Nominal.NPrf (syn_wb (.classEq (syn_cdm A) (syn_c0)) (.classEq (syn_crn A) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_c0)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_alnex (syn_wex y (syn_wbr (.cv x) A (.cv y))) x
  have p0001 :=
    @g_excom (syn_wbr (.cv x) A (.cv y)) x y
  have p0002 :=
    @g_xchbinx (.all x (.neg (syn_wex y (syn_wbr (.cv x) A (.cv y))))) (syn_wex x (syn_wex y (syn_wbr (.cv x) A (.cv y)))) (syn_wex y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) p0000 p0001
  have p0003 :=
    @g_alnex (syn_wex x (syn_wbr (.cv x) A (.cv y))) y
  have p0004 :=
    @g_bitr4i (.all x (.neg (syn_wex y (syn_wbr (.cv x) A (.cv y))))) (.neg (syn_wex y (syn_wex x (syn_wbr (.cv x) A (.cv y))))) (.all y (.neg (syn_wex x (syn_wbr (.cv x) A (.cv y))))) p0002 p0003
  have p0005 :=
    @g_noel (.cv x)
  have p0006 :=
    @g_nbn (.classMem (.cv x) (syn_c0)) (syn_wex y (syn_wbr (.cv x) A (.cv y))) p0005
  have p0007 :=
    @g_albii (.neg (syn_wex y (syn_wbr (.cv x) A (.cv y)))) (syn_wb (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) (syn_c0))) x p0006
  have p0008 :=
    @g_noel (.cv y)
  have p0009 :=
    @g_nbn (.classMem (.cv y) (syn_c0)) (syn_wex x (syn_wbr (.cv x) A (.cv y))) p0008
  have p0010 :=
    @g_albii (.neg (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (syn_wb (syn_wex x (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv y) (syn_c0))) y p0009
  have p0011 :=
    @g_n_3bitr3i (.all x (.neg (syn_wex y (syn_wbr (.cv x) A (.cv y))))) (.all y (.neg (syn_wex x (syn_wbr (.cv x) A (.cv y))))) (.all x (syn_wb (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) (syn_c0)))) (.all y (syn_wb (syn_wex x (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv y) (syn_c0)))) p0004 p0007 p0010
  have p0012 :=
    @g_eqabcb (syn_wex y (syn_wbr (.cv x) A (.cv y))) x (syn_c0) dv_cache_0001
  have p0013 :=
    @g_eqabcb (syn_wex x (syn_wbr (.cv x) A (.cv y))) y (syn_c0) dv_cache_0002
  have p0014 :=
    @g_n_3bitr4i (.all x (syn_wb (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) (syn_c0)))) (.all y (syn_wb (syn_wex x (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv y) (syn_c0)))) (.classEq (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y)))) (syn_c0)) (.classEq (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (syn_c0)) p0011 p0012 p0013
  have p0015 :=
    @g_dfdm2 x y A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0016 :=
    @g_eqeq1i (syn_cdm A) (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y)))) (syn_c0) p0015
  have p0017 :=
    @g_dfrn2 x y A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0018 :=
    @g_eqeq1i (syn_crn A) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (syn_c0) p0017
  have p0019 :=
    @g_n_3bitr4i (.classEq (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y)))) (syn_c0)) (.classEq (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (syn_c0)) (.classEq (syn_cdm A) (syn_c0)) (.classEq (syn_crn A) (syn_c0)) p0014 p0016 p0018
  exact p0019

noncomputable def g_dmeq0
    (A : Class) :
    Nominal.NPrf (syn_wb (.classEq A (syn_c0)) (.classEq (syn_cdm A) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cdm A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_eldm2 y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_notbii (.classMem (.cv x) (syn_cdm A)) (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)) p0000
  have p0002 :=
    @g_alnex (.classMem (syn_cop (.cv x) (.cv y)) A) y
  have p0003 :=
    @g_noel (syn_cop (.cv x) (.cv y))
  have p0004 :=
    @g_nbn (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0)) (.classMem (syn_cop (.cv x) (.cv y)) A) p0003
  have p0005 :=
    @g_albii (.neg (.classMem (syn_cop (.cv x) (.cv y)) A)) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0))) y p0004
  have p0006 :=
    @g_n_3bitr2i (.neg (.classMem (.cv x) (syn_cdm A))) (.neg (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A))) (.all y (.neg (.classMem (syn_cop (.cv x) (.cv y)) A))) (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0)))) p0001 p0002 p0005
  have p0007 :=
    @g_albii (.neg (.classMem (.cv x) (syn_cdm A))) (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0)))) x p0006
  have p0008 :=
    @g_eq0 x (syn_cdm A) dv_cache_0003
  have p0009 :=
    @g_eqrel x y A (syn_c0) dv_cache_0004 dv_cache_0002 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0010 :=
    @g_n_3bitr4ri (.all x (.neg (.classMem (.cv x) (syn_cdm A)))) (.all x (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0))))) (.classEq (syn_cdm A) (syn_c0)) (.classEq A (syn_c0)) p0007 p0008 p0009
  exact p0010

noncomputable def g_dmxp
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wne B (syn_c0)) (.classEq (syn_cdm (syn_cxp A B)) A)) := by
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
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : y ∉ ((syn_wne B (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp y x A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_dmeqi (syn_cxp A B) (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B))) p0000
  have p0002 :=
    @g_n0 x B dv_cache_0004
  have p0003 :=
    @g_biimpi (syn_wne B (syn_c0)) (syn_wex x (.classMem (.cv x) B)) p0002
  have p0004 :=
    @g_ralrimivw (syn_wne B (syn_c0)) (syn_wex x (.classMem (.cv x) B)) y A dv_cache_0006 p0003
  have p0005 :=
    @g_dmopab3 (.classMem (.cv x) B) y x A dv_cache_0001 dv_cache_0002 dv_cache_0005
  have p0006 :=
    @g_sylib (syn_wne B (syn_c0)) (syn_wral y A (syn_wex x (.classMem (.cv x) B))) (.classEq (syn_cdm (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)))) A) p0004 p0005
  have p0007 :=
    @g_syl5eq (syn_wne B (syn_c0)) (syn_cdm (syn_cxp A B)) (syn_cdm (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)))) A p0001 p0006
  exact p0007

noncomputable def g_reseq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cres A C) (syn_cres B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ineq1 A B (syn_cxp C (syn_cvv))
  have p0001 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres A C)))
  have p0002 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres B C)))
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cin A (syn_cxp C (syn_cvv))) (syn_cin B (syn_cxp C (syn_cvv))) (syn_cres A C) (syn_cres B C) p0000 p0001 p0002
  exact p0003

noncomputable def g_reseq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cres C A) (syn_cres C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_xpeq1 A B (syn_cvv)
  have p0001 :=
    @g_ineq2d (.classEq A B) (syn_cxp A (syn_cvv)) (syn_cxp B (syn_cvv)) C p0000
  have p0002 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres C A)))
  have p0003 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres C B)))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cin C (syn_cxp A (syn_cvv))) (syn_cin C (syn_cxp B (syn_cvv))) (syn_cres C A) (syn_cres C B) p0001 p0002 p0003
  exact p0004

noncomputable def g_reseq1i
    (A : Class) (B : Class) (C : Class) (hyp_reseqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cres A C) (syn_cres B C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_reseq1 A B C
  have p0001 :=
    Nominal.mp hyp_reseqi_1 p0000
  exact p0001

noncomputable def g_reseq2i
    (A : Class) (B : Class) (C : Class) (hyp_reseqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cres C A) (syn_cres C B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_reseq2 A B C
  have p0001 :=
    Nominal.mp hyp_reseqi_1 p0000
  exact p0001

noncomputable def g_reseq12i
    (A : Class) (B : Class) (C : Class) (D : Class) (hyp_reseqi_1 : Nominal.NPrf (.classEq A B)) (hyp_reseqi_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cres A C) (syn_cres B D)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_reseq1i A B C hyp_reseqi_1
  have p0001 :=
    @g_reseq2i C D B hyp_reseqi_2
  have p0002 :=
    @g_eqtri (syn_cres A C) (syn_cres B C) (syn_cres B D) p0000 p0001
  exact p0002

noncomputable def g_reseq2d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_reseqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cres C A) (syn_cres C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_reseq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cres C A) (syn_cres C B)) hyp_reseqd_1 p0000
  exact p0001

noncomputable def g_imaeq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cima A C) (syn_cima B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ∉ ((Wff.classEq A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_breq (.cv y) (.cv x) A B
  have p0001 :=
    @g_rexbidv (.classEq A B) (syn_wbr (.cv y) A (.cv x)) (syn_wbr (.cv y) B (.cv x)) y C dv_cache_0001 p0000
  have p0002 :=
    @g_abbidv (.classEq A B) (syn_wrex y C (syn_wbr (.cv y) A (.cv x))) (syn_wrex y C (syn_wbr (.cv y) B (.cv x))) x dv_cache_0002 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y A C dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y B C dv_cache_0008 dv_cache_0009 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wrex y C (syn_wbr (.cv y) A (.cv x)))) (.cab x (syn_wrex y C (syn_wbr (.cv y) B (.cv x)))) (syn_cima A C) (syn_cima B C) p0002 p0003 p0004
  exact p0005

noncomputable def g_imaeq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cima C A) (syn_cima C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_rexeq (syn_wbr (.cv y) C (.cv x)) y A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wrex y A (syn_wbr (.cv y) C (.cv x))) (syn_wrex y B (syn_wbr (.cv y) C (.cv x))) x dv_cache_0003 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y C A dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0001 dv_cache_0007
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y C B dv_cache_0004 dv_cache_0005 dv_cache_0008 dv_cache_0002 dv_cache_0007
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wrex y A (syn_wbr (.cv y) C (.cv x)))) (.cab x (syn_wrex y B (syn_wbr (.cv y) C (.cv x)))) (syn_cima C A) (syn_cima C B) p0001 p0002 p0003
  exact p0004

noncomputable def g_imaeq1i
    (A : Class) (B : Class) (C : Class) (hyp_imaeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cima A C) (syn_cima B C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_imaeq1 A B C
  have p0001 :=
    Nominal.mp hyp_imaeq1i_1 p0000
  exact p0001

noncomputable def g_imaeq2i
    (A : Class) (B : Class) (C : Class) (hyp_imaeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cima C A) (syn_cima C B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_imaeq2 A B C
  have p0001 :=
    Nominal.mp hyp_imaeq1i_1 p0000
  exact p0001

noncomputable def g_imaeq1d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_imaeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cima A C) (syn_cima B C))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_imaeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cima A C) (syn_cima B C)) hyp_imaeq1d_1 p0000
  exact p0001

noncomputable def g_imaeq2d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_imaeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cima C A) (syn_cima C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_imaeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cima C A) (syn_cima C B)) hyp_imaeq1d_1 p0000
  exact p0001

#print axioms g_imaeq2d

end NFChoice.DirectNominalPrf.WPPReplay
