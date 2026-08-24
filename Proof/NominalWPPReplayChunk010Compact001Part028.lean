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
import NominalWPPReplayChunk010Compact001Part027

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

noncomputable def g_dfphi2
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cphi A) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A)) := by
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
  have dv_cache_0001 : y ∉ ((Wff.objEq z x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0005 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cphi A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_iftrue (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0001 :=
    @g_eqeq2d (.classMem (.cv y) (syn_cnnc)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (syn_cplc (.cv y) (syn_c1c)) (.cv x) p0000
  have p0002 :=
    @g_iba (.classMem (.cv y) (syn_cnnc)) (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
  have p0003 :=
    @g_simpr (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))
  have p0004 :=
    @g_con2i (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))) (.classMem (.cv y) (syn_cnnc)) p0003
  have p0005 :=
    @g_biorf (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))) (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
  have p0006 :=
    @g_syl (.classMem (.cv y) (syn_cnnc)) (.neg (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))) (syn_wb (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wo (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))) (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))))) p0004 p0005
  have p0007 :=
    @g_orcom (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))) (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
  have p0008 :=
    @g_syl6bb (.classMem (.cv y) (syn_cnnc)) (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wo (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))) (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))) (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))) p0006 p0007
  have p0009 :=
    @g_n_3bitrd (.classMem (.cv y) (syn_cnnc)) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))) p0001 p0002 p0008
  have p0010 :=
    @g_iffalse (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0011 :=
    @g_eqeq2d (.neg (.classMem (.cv y) (syn_cnnc))) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (.cv y) (.cv x) p0010
  have p0012 :=
    @g_iba (.neg (.classMem (.cv y) (syn_cnnc))) (.objEq x y)
  have p0013 :=
    @g_simpr (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))
  have p0014 :=
    @g_con3i (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)) p0013
  have p0015 :=
    @g_biorf (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))
  have p0016 :=
    @g_syl (.neg (.classMem (.cv y) (syn_cnnc))) (.neg (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))) (syn_wb (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))) (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))))) p0014 p0015
  have p0017_e00_recanon : Nominal.NPrf (.imp (.neg (.classMem (.cv y) (syn_cnnc))) (syn_wb (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cnnc syn_cint syn_wa syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_wral syn_cplc syn_wrex syn_wex syn_c1c syn_wb syn_cif syn_wo
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
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
      p0011
  have p0017 :=
    @g_n_3bitrd (.neg (.classMem (.cv y) (syn_cnnc))) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.objEq x y) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))) (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))) p0017_e00_recanon p0012 p0016
  have p0018 :=
    @g_pm2_61i (.classMem (.cv y) (syn_cnnc)) (syn_wb (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))))) p0009 p0017
  have p0019 :=
    @g_equcom y x
  have p0020 :=
    @g_vex y
  have p0021 :=
    @g_elcompl (.cv y) (syn_cnnc) p0020
  have p0022 :=
    @g_anbi12i (.objEq y x) (.objEq x y) (.classMem (.cv y) (syn_ccompl (syn_cnnc))) (.neg (.classMem (.cv y) (syn_cnnc))) p0019 p0021
  have p0023 :=
    @g_orbi2i (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc)))) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))) (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) p0022
  have p0024 :=
    @g_bitr4i (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))) (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc))))) p0018 p0023
  have p0025 :=
    @g_elun (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))
  have p0026 :=
    @g_elin (syn_copk (.cv y) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))
  have p0027 :=
    @g_vex x
  have p0028 :=
    @g_opkelimagek (.cv y) (.cv x) (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0020 p0027
  have p0029 :=
    @g_dfaddc2 (.cv y) (syn_c1c)
  have p0030 :=
    @g_eqeq2i (syn_cplc (.cv y) (syn_c1c)) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv y)) (.cv x) p0029
  have p0031 :=
    @g_bitr4i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq (.cv x) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv y))) (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) p0028 p0030
  have p0032 :=
    @g_opkelxpk (.cv y) (.cv x) (syn_cnnc) (syn_cvv) p0020 p0027
  have p0033 :=
    @g_mpbiran2 (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_cnnc) (syn_cvv))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0027 p0032
  have p0034 :=
    @g_anbi12i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_cnnc) (syn_cvv))) (.classMem (.cv y) (syn_cnnc)) p0031 p0033
  have p0035 :=
    @g_bitri (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))) (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_cnnc) (syn_cvv)))) (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) p0026 p0034
  have p0036 :=
    @g_elin (syn_copk (.cv y) (.cv x)) (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))
  have p0037 :=
    @g_opkelidkg (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0038_e02_recanon : Nominal.NPrf (.imp (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv))) (syn_wb (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cvv syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cidk syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
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
      p0037
  have p0038 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq y x)) p0020 p0027 p0038_e02_recanon
  have p0039 :=
    @g_opkelxpk (.cv y) (.cv x) (syn_ccompl (syn_cnnc)) (syn_cvv) p0020 p0027
  have p0040 :=
    @g_mpbiran2 (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))) (.classMem (.cv y) (syn_ccompl (syn_cnnc))) (.classMem (.cv x) (syn_cvv)) p0027 p0039
  have p0041 :=
    @g_anbi12i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq y x) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))) (.classMem (.cv y) (syn_ccompl (syn_cnnc))) p0038 p0040
  have p0042 :=
    @g_bitri (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc)))) p0036 p0041
  have p0043 :=
    @g_orbi12i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))) (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc)))) p0035 p0042
  have p0044 :=
    @g_bitri (.classMem (syn_copk (.cv y) (.cv x)) (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))) (syn_wo (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))) (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc))))) p0025 p0043
  have p0045 :=
    @g_bitr4i (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc))))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))) p0024 p0044
  have p0046 :=
    @g_rexbii (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))) y A p0045
  have p0047 :=
    @g_eqeq1 (.cv z) (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))
  have p0048_e00_recanon : Nominal.NPrf (.imp (.objEq z x) (syn_wb (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cif syn_wo syn_wa syn_cnnc syn_cint syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0047
  have p0048 :=
    @g_rexbidv (.objEq z x) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) y A dv_cache_0001 p0048_e00_recanon
  have p0049 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y z A dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0050_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv z) (.cv x)) (syn_wb (syn_wrex y A (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0048
  have p0050 :=
    @g_elab2 (syn_wrex y A (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) z (.cv x) (syn_cphi A) dv_cache_0005 dv_cache_0006 p0027 p0050_e01_recanon p0049
  have p0051 :=
    @g_elimak y (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A (.cv x) dv_cache_0007 dv_cache_0002 dv_cache_0008 p0027
  have p0052 :=
    @g_n_3bitr4i (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (.classMem (.cv x) (syn_cphi A)) (.classMem (.cv x) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A)) p0046 p0050 p0051
  have p0053 :=
    @g_eqriv x (syn_cphi A) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A) dv_cache_0009 dv_cache_0010 p0052
  exact p0053

noncomputable def g_phieq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cphi A) (syn_cphi B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_imakeq2 A B (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
  have p0001 :=
    @g_dfphi2 A
  have p0002 :=
    @g_dfphi2 B
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) B) (syn_cphi A) (syn_cphi B) p0000 p0001 p0002
  exact p0003

noncomputable def g_phiexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cphi A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_dfphi2 A
  have p0001 :=
    @g_addcexlem
  have p0002 :=
    @g_n_1cex
  have p0003 :=
    @g_pw1ex (syn_c1c) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0003
  have p0005 :=
    @g_imakex (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0001 p0004
  have p0006 :=
    @g_imagekex (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0005
  have p0007 :=
    @g_nncex
  have p0008 :=
    @g_vvex
  have p0009 :=
    @g_xpkex (syn_cnnc) (syn_cvv) p0007 p0008
  have p0010 :=
    @g_inex (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)) p0006 p0009
  have p0011 :=
    @g_idkex
  have p0012 :=
    @g_nncex
  have p0013 :=
    @g_complex (syn_cnnc) p0012
  have p0014 :=
    @g_vvex
  have p0015 :=
    @g_xpkex (syn_ccompl (syn_cnnc)) (syn_cvv) p0013 p0014
  have p0016 :=
    @g_inex (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)) p0011 p0015
  have p0017 :=
    @g_unex (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))) p0010 p0016
  have p0018 :=
    @g_imakexg (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A (syn_cvv) V
  have p0019 :=
    @g_mpan (.classMem (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (syn_cvv)) (.classMem A V) (.classMem (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A) (syn_cvv)) p0017 p0018
  have p0020 :=
    @g_syl5eqel (.classMem A V) (syn_cphi A) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A) (syn_cvv) p0000 p0019
  exact p0020

noncomputable def g_phiex
    (A : Class) (hyp_phiex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cphi A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_phiexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_phiex_1 p0000
  exact p0001

#print axioms g_phiex

end NFChoice.DirectNominalPrf.WPPReplay
