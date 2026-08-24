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
import NominalWPPReplayChunk011Compact001Part008

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

noncomputable def g_ssdmrn
    (A : Class) :
    Nominal.NPrf (syn_wss A (syn_cxp (syn_cdm A) (syn_crn A))) := by
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
  have dv_cache_0003 : x ∉ ((syn_cxp (syn_cdm A) (syn_crn A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cxp (syn_cdm A) (syn_crn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_ssrel x y A (syn_cxp (syn_cdm A) (syn_crn A)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_opeldm (.cv x) (.cv y) A
  have p0002 :=
    @g_opelrn (.cv x) (.cv y) A
  have p0003 :=
    @g_opelxp (.cv x) (.cv y) (syn_cdm A) (syn_crn A)
  have p0004 :=
    @g_sylanbrc (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (.cv x) (syn_cdm A)) (.classMem (.cv y) (syn_crn A)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cdm A) (syn_crn A))) p0001 p0002 p0003
  have p0005 :=
    Nominal.gen p0004 y
  have p0006 :=
    @g_mpgbir (syn_wss A (syn_cxp (syn_cdm A) (syn_crn A))) (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cdm A) (syn_crn A))))) x p0000 p0005
  exact p0006

noncomputable def g_dfcnv2
    (A : Class) :
    Nominal.NPrf (.classEq (syn_ccnv A) (syn_cima (syn_cswap) A)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((syn_cop (.cv y) (.cv x))).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classMem (syn_cop (.cv y) (.cv x)) A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_cswap)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_ccnv A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_ccnv A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cima (syn_cswap) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cima (syn_cswap) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_brswap2 (.cv z) (.cv x) (.cv y) p0000 p0001
  have p0003 :=
    @g_anbi1i (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))) (.classEq (.cv z) (syn_cop (.cv y) (.cv x))) (.classMem (.cv z) A) p0002
  have p0004 :=
    @g_exbii (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))) (.classMem (.cv z) A)) (syn_wa (.classEq (.cv z) (syn_cop (.cv y) (.cv x))) (.classMem (.cv z) A)) z p0003
  have p0005 :=
    @g_opex (.cv y) (.cv x) p0001 p0000
  have p0006 :=
    @g_eleq1 (.cv z) (syn_cop (.cv y) (.cv x)) A
  have p0007 :=
    @g_ceqsexv (.classMem (.cv z) A) (.classMem (syn_cop (.cv y) (.cv x)) A) z (syn_cop (.cv y) (.cv x)) dv_cache_0001 dv_cache_0002 p0005 p0006
  have p0008 :=
    @g_bitri (syn_wex z (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))) (.classMem (.cv z) A))) (syn_wex z (syn_wa (.classEq (.cv z) (syn_cop (.cv y) (.cv x))) (.classMem (.cv z) A))) (.classMem (syn_cop (.cv y) (.cv x)) A) p0004 p0007
  have p0009 :=
    @g_elima z (syn_cop (.cv x) (.cv y)) (syn_cswap) A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0010 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex z A (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))))))
  have p0011 :=
    @g_exancom (.classMem (.cv z) A) (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))) z
  have p0012 :=
    @g_bitri (syn_wrex z A (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y)))) (syn_wex z (syn_wa (.classMem (.cv z) A) (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))))) (syn_wex z (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))) (.classMem (.cv z) A))) p0010 p0011
  have p0013 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_cima (syn_cswap) A)) (syn_wrex z A (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y)))) (syn_wex z (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))) (.classMem (.cv z) A))) p0009 p0012
  have p0014 :=
    @g_opelcnv (.cv x) (.cv y) A
  have p0015 :=
    @g_n_3bitr4ri (syn_wex z (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))) (.classMem (.cv z) A))) (.classMem (syn_cop (.cv y) (.cv x)) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cima (syn_cswap) A)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv A)) p0008 p0013 p0014
  have p0016 :=
    @g_eqrelriv x y (syn_ccnv A) (syn_cima (syn_cswap) A) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0015
  exact p0016

noncomputable def g_cnvexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_ccnv A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_dfcnv2 A
  have p0001 :=
    @g_swapex
  have p0002 :=
    @g_imaexg (syn_cswap) A (syn_cvv) V
  have p0003 :=
    @g_mpan (.classMem (syn_cswap) (syn_cvv)) (.classMem A V) (.classMem (syn_cima (syn_cswap) A) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_ccnv A) (syn_cima (syn_cswap) A) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_cnvex
    (A : Class) (hyp_cnvex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ccnv A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_cnvexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_cnvex_1 p0000
  exact p0001

noncomputable def g_rnexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_crn A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_crn] using (Nominal.classEqRefl (syn_crn A)))
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_imaexg A (syn_cvv) V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem A V) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cima A (syn_cvv)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_crn A) (syn_cima A (syn_cvv)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_dmexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cdm A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_cdm] using (Nominal.classEqRefl (syn_cdm A)))
  have p0001 :=
    @g_cnvexg A V
  have p0002 :=
    @g_rnexg (syn_ccnv A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A V) (.classMem (syn_ccnv A) (syn_cvv)) (.classMem (syn_crn (syn_ccnv A)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_cdm A) (syn_crn (syn_ccnv A)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_dmex
    (A : Class) (hyp_dmex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cdm A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_dmexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_dmex_1 p0000
  exact p0001

noncomputable def g_rnex
    (A : Class) (hyp_dmex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_crn A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_rnexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_dmex_1 p0000
  exact p0001

noncomputable def g_df2nd2
     :
    Nominal.NPrf (.classEq (syn_c2nd) (syn_ccom (syn_c1st) (syn_cswap))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have dv_cache_0001 : z ∉ ((Class.cv w)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wbr (.cv x) (syn_cswap) (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_wbr (.cv x) (syn_cswap) (syn_cop (.cv y) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cswap)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cswap)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((syn_cswap)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0016 : y ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have p0000 :=
    @g_vex y
  have p0001 :=
    @g_br1st z (.cv w) (.cv y) dv_cache_0001 dv_cache_0002 p0000
  have p0002 :=
    @g_anbi1i (syn_wbr (.cv w) (syn_c1st) (.cv y)) (syn_wex z (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))) (syn_wbr (.cv x) (syn_cswap) (.cv w)) p0001
  have p0003 :=
    @g_ancom (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y))
  have p0004 :=
    @g_n_19_41v (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_cswap) (.cv w)) z dv_cache_0003
  have p0005 :=
    @g_n_3bitr4i (syn_wa (syn_wbr (.cv w) (syn_c1st) (.cv y)) (syn_wbr (.cv x) (syn_cswap) (.cv w))) (syn_wa (syn_wex z (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))) (syn_wbr (.cv x) (syn_cswap) (.cv w))) (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y))) (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_cswap) (.cv w)))) p0002 p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y))) (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_cswap) (.cv w)))) w p0005
  have p0007 :=
    @g_excom (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_cswap) (.cv w))) z w
  have p0008 :=
    @g_vex z
  have p0009 :=
    @g_opex (.cv y) (.cv z) p0000 p0008
  have p0010 :=
    @g_breq2 (.cv w) (syn_cop (.cv y) (.cv z)) (.cv x) (syn_cswap)
  have p0011 :=
    @g_ceqsexv (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv x) (syn_cswap) (syn_cop (.cv y) (.cv z))) w (syn_cop (.cv y) (.cv z)) dv_cache_0004 dv_cache_0005 p0009 p0010
  have p0012 :=
    @g_brswap2 (.cv x) (.cv y) (.cv z) p0000 p0008
  have p0013 :=
    @g_bitri (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_cswap) (.cv w)))) (syn_wbr (.cv x) (syn_cswap) (syn_cop (.cv y) (.cv z))) (.classEq (.cv x) (syn_cop (.cv z) (.cv y))) p0011 p0012
  have p0014 :=
    @g_exbii (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_cswap) (.cv w)))) (.classEq (.cv x) (syn_cop (.cv z) (.cv y))) z p0013
  have p0015 :=
    @g_n_3bitr2ri (syn_wex w (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y)))) (syn_wex w (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_cswap) (.cv w))))) (syn_wex z (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_cswap) (.cv w))))) (syn_wex z (.classEq (.cv x) (syn_cop (.cv z) (.cv y)))) p0006 p0007 p0014
  have p0016 :=
    @g_opabbii (syn_wex z (.classEq (.cv x) (syn_cop (.cv z) (.cv y)))) (syn_wex w (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y)))) x y p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_2nd x y z dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co x y w (syn_c1st) (syn_cswap) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0006 dv_cache_0015 dv_cache_0016
  have p0019 :=
    @g_n_3eqtr4i (syn_copab x y (syn_wex z (.classEq (.cv x) (syn_cop (.cv z) (.cv y))))) (syn_copab x y (syn_wex w (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y))))) (syn_c2nd) (syn_ccom (syn_c1st) (syn_cswap)) p0016 p0017 p0018
  exact p0019

noncomputable def g_n_2ndex
     :
    Nominal.NPrf (.classMem (syn_c2nd) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_df2nd2
  have p0001 :=
    @g_n_1stex
  have p0002 :=
    @g_swapex
  have p0003 :=
    @g_coex (syn_c1st) (syn_cswap) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_c2nd) (syn_ccom (syn_c1st) (syn_cswap)) (syn_cvv) p0000 p0003
  exact p0004

#print axioms g_n_2ndex

end NFChoice.DirectNominalPrf.WPPReplay
