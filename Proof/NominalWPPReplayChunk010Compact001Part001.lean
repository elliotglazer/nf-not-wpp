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
import NominalWPPReplayChunk009

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

noncomputable def g_oddnn
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_coddfin)) (.classMem A (syn_cnnc))) := by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.classMem A (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqeq1 (.cv x) A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) n (syn_cnnc) dv_cache_0001 p0000
  have p0002 :=
    @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x n dv_cache_0002
  have p0005 :=
    @g_elab2g (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0))) x A (syn_coddfin) (syn_coddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_coddfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0))) p0005
  have p0007 :=
    @g_nncaddccl (.cv n) (.cv n)
  have p0008 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0007
  have p0009 :=
    @g_peano2 (syn_cplc (.cv n) (.cv n))
  have p0010 :=
    @g_eleq1a (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cnnc) A
  have p0011 :=
    @g_n_3syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cnnc)) (.imp (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.classMem A (syn_cnnc))) p0008 p0009 p0010
  have p0012 :=
    @g_rexlimiv (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.classMem A (syn_cnnc)) n (syn_cnnc) dv_cache_0005 p0011
  have p0013 :=
    @g_adantr (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)) p0012
  have p0014 :=
    @g_syl (.classMem A (syn_coddfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0))) (.classMem A (syn_cnnc)) p0006 p0013
  exact p0014

noncomputable def g_evennnul
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cevenfin)) (syn_wne A (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne A (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqeq1 (.cv x) A (syn_cplc (.cv n) (.cv n))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (.classEq A (syn_cplc (.cv n) (.cv n))) n (syn_cnnc) dv_cache_0001 p0000
  have p0002 :=
    @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x n dv_cache_0002
  have p0005 :=
    @g_elab2g (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne A (syn_c0))) x A (syn_cevenfin) (syn_cevenfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_cevenfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne A (syn_c0))) p0005
  have p0007 :=
    @g_simprd (.classMem A (syn_cevenfin)) (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne A (syn_c0)) p0006
  exact p0007

noncomputable def g_oddnnul
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_coddfin)) (syn_wne A (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqeq1 (.cv x) A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) n (syn_cnnc) dv_cache_0001 p0000
  have p0002 :=
    @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x n dv_cache_0002
  have p0005 :=
    @g_elab2g (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0))) x A (syn_coddfin) (syn_coddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_coddfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0))) p0005
  have p0007 :=
    @g_simprd (.classMem A (syn_coddfin)) (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)) p0006
  exact p0007

noncomputable def g_sucevenodd
    (A : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cevenfin)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))) (.classMem (syn_cplc A (syn_c1c)) (syn_coddfin))) := by
  let proofSupport : Finset Var := A.fv
  let m : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_m_ne_x : m ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_m : x ≠ m :=
    Ne.symm fresh_m_ne_x
  have dv_cache_0001 : m ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_x, fresh_m_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : m ≠ x := by
    clear dv_cache_0001
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m)))) (syn_wne A (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((Wff.classEq (.cv x) (syn_cplc A (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_x, fresh_m_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cplc A (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqeq1 (.cv x) A (syn_cplc (.cv m) (.cv m))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m))) (.classEq A (syn_cplc (.cv m) (.cv m))) m (syn_cnnc) dv_cache_0001 p0000
  have p0002 :=
    @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m)))) (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m)))) (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x m dv_cache_0002
  have p0005 :=
    @g_elab2g (syn_wa (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m)))) (syn_wne A (syn_c0))) x A (syn_cevenfin) (syn_cevenfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_cevenfin)) (syn_wa (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m)))) (syn_wne A (syn_c0))) p0005
  have p0007 :=
    @g_addceq1 A (syn_cplc (.cv m) (.cv m)) (syn_c1c)
  have p0008 :=
    @g_reximi (.classEq A (syn_cplc (.cv m) (.cv m))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))) m (syn_cnnc) p0007
  have p0009 :=
    @g_adantr (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m)))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne A (syn_c0)) p0008
  have p0010 :=
    @g_syl (.classMem A (syn_cevenfin)) (syn_wa (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m)))) (syn_wne A (syn_c0))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) p0006 p0009
  have p0011 :=
    @g_anim1i (.classMem A (syn_cevenfin)) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0010
  have p0012 :=
    @g_n_1cex
  have p0013 :=
    @g_addcexg A (syn_c1c) (syn_cevenfin) (syn_cvv)
  have p0014 :=
    @g_mpan2 (.classMem A (syn_cevenfin)) (.classMem (syn_c1c) (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_eqeq1 (.cv x) (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))
  have p0016 :=
    @g_rexbidv (.classEq (.cv x) (syn_cplc A (syn_c1c))) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))) m (syn_cnnc) dv_cache_0005 p0015
  have p0017 :=
    @g_neeq1 (.cv x) (syn_cplc A (syn_c1c)) (syn_c0)
  have p0018 :=
    @g_anbi12d (.classEq (.cv x) (syn_cplc A (syn_c1c))) (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0016 p0017
  have p0019 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x m dv_cache_0002
  have p0020 :=
    @g_elab2g (syn_wa (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))) x (syn_cplc A (syn_c1c)) (syn_coddfin) (syn_cvv) dv_cache_0006 dv_cache_0007 p0018 p0019
  have p0021 :=
    @g_syl (.classMem A (syn_cevenfin)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (syn_wb (.classMem (syn_cplc A (syn_c1c)) (syn_coddfin)) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))) p0014 p0020
  have p0022 :=
    @g_adantr (.classMem A (syn_cevenfin)) (syn_wb (.classMem (syn_cplc A (syn_c1c)) (syn_coddfin)) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0021
  have p0023 :=
    @g_mpbird (syn_wa (.classMem A (syn_cevenfin)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))) (.classMem (syn_cplc A (syn_c1c)) (syn_coddfin)) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))) p0011 p0022
  exact p0023

noncomputable def g_sucoddeven
    (A : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_coddfin)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))) (.classMem (syn_cplc A (syn_c1c)) (syn_cevenfin))) := by
  let proofSupport : Finset Var := A.fv
  let m : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_m_ne_n : m ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_m : n ≠ m :=
    Ne.symm fresh_m_ne_n
  have fresh_m_ne_x : m ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_m : x ≠ m :=
    Ne.symm fresh_m_ne_x
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((syn_cplc (.cv n) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : m ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : m ∉ ((Wff.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((Wff.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_A, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_A, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((Wff.classEq (.cv x) (syn_cplc A (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_x, fresh_m_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : m ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0012 : x ∉ ((syn_cplc A (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqeq1 (.cv x) A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) n (syn_cnnc) dv_cache_0001 p0000
  have p0002 :=
    @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x n dv_cache_0002
  have p0005 :=
    @g_elab2g (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0))) x A (syn_coddfin) (syn_coddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_coddfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0))) p0005
  have p0007 :=
    @g_peano2 (.cv n)
  have p0008 :=
    @g_addc32 (.cv n) (.cv n) (syn_c1c)
  have p0009 :=
    @g_addceq1i (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (.cv n)) (syn_c1c) p0008
  have p0010 :=
    @g_addcass (syn_cplc (.cv n) (syn_c1c)) (.cv n) (syn_c1c)
  have p0011 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (.cv n)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) p0009 p0010
  have p0012 :=
    @g_addceq12 (.cv m) (.cv m) (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
  have p0013 :=
    @g_anidms (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (.classEq (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) p0012
  have p0014 :=
    @g_eqeq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv m) (.cv m)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) p0013
  have p0015 :=
    @g_rspcev (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (.cv m) (.cv m))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) m (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0014
  have p0016 :=
    @g_mpan2 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) p0011 p0015
  have p0017 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) p0007 p0016
  have p0018 :=
    @g_addceq1 A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)
  have p0019 :=
    @g_eqeq1d (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (.cv m) (.cv m)) p0018
  have p0020 :=
    @g_rexbidv (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (.cv m) (.cv m))) m (syn_cnnc) dv_cache_0008 p0019
  have p0021 :=
    @g_biimprd (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) p0020
  have p0022 :=
    @g_com12 (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) p0021
  have p0023 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (.imp (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))) p0017 p0022
  have p0024 :=
    @g_rexlimiv (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) n (syn_cnnc) dv_cache_0009 p0023
  have p0025 :=
    @g_adantr (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wne A (syn_c0)) p0024
  have p0026 :=
    @g_syl (.classMem A (syn_coddfin)) (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) p0006 p0025
  have p0027 :=
    @g_anim1i (.classMem A (syn_coddfin)) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0026
  have p0028 :=
    @g_n_1cex
  have p0029 :=
    @g_addcexg A (syn_c1c) (syn_coddfin) (syn_cvv)
  have p0030 :=
    @g_mpan2 (.classMem A (syn_coddfin)) (.classMem (syn_c1c) (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0028 p0029
  have p0031 :=
    @g_eqeq1 (.cv x) (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))
  have p0032 :=
    @g_rexbidv (.classEq (.cv x) (syn_cplc A (syn_c1c))) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))) m (syn_cnnc) dv_cache_0010 p0031
  have p0033 :=
    @g_neeq1 (.cv x) (syn_cplc A (syn_c1c)) (syn_c0)
  have p0034 :=
    @g_anbi12d (.classEq (.cv x) (syn_cplc A (syn_c1c))) (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m)))) (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0032 p0033
  have p0035 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x m dv_cache_0011
  have p0036 :=
    @g_elab2g (syn_wa (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m)))) (syn_wne (.cv x) (syn_c0))) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))) x (syn_cplc A (syn_c1c)) (syn_cevenfin) (syn_cvv) dv_cache_0012 dv_cache_0013 p0034 p0035
  have p0037 :=
    @g_syl (.classMem A (syn_coddfin)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (syn_wb (.classMem (syn_cplc A (syn_c1c)) (syn_cevenfin)) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))) p0030 p0036
  have p0038 :=
    @g_adantr (.classMem A (syn_coddfin)) (syn_wb (.classMem (syn_cplc A (syn_c1c)) (syn_cevenfin)) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0037
  have p0039 :=
    @g_mpbird (syn_wa (.classMem A (syn_coddfin)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))) (.classMem (syn_cplc A (syn_c1c)) (syn_cevenfin)) (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))) p0027 p0038
  exact p0039

noncomputable def g_dfevenfin2
    (x : Var) (n : Var) (dv_n_x : n ≠ x) :
    Nominal.NPrf (.classEq (syn_cevenfin) (.cab x (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({n} : Finset Var)
  have dv_cache_0001 : n ≠ x := by
    exact (show n ≠ x from (by exact dv_n_x))
  have dv_cache_0002 : n ∉ ((syn_wne (.cv x) (syn_c0))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_n_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x n dv_cache_0001
  have p0001 :=
    @g_r19_41v (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (.cv x) (syn_c0)) n (syn_cnnc) dv_cache_0002
  have p0002 :=
    @g_neeq1 (.cv x) (syn_cplc (.cv n) (.cv n)) (syn_c0)
  have p0003 :=
    @g_pm5_32i (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) p0002
  have p0004 :=
    @g_rexbii (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (.cv x) (syn_c0))) (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0))) n (syn_cnnc) p0003
  have p0005 :=
    @g_bitr3i (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (.cv x) (syn_c0)))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)))) p0001 p0004
  have p0006 :=
    @g_abbii (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)))) x p0005
  have p0007 :=
    @g_eqtri (syn_cevenfin) (.cab x (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) (syn_wne (.cv x) (syn_c0)))) (.cab x (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0))))) p0000 p0006
  exact p0007

noncomputable def g_dfoddfin2
    (x : Var) (n : Var) (dv_n_x : n ≠ x) :
    Nominal.NPrf (.classEq (syn_coddfin) (.cab x (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({n} : Finset Var)
  have dv_cache_0001 : n ≠ x := by
    exact (show n ≠ x from (by exact dv_n_x))
  have dv_cache_0002 : n ∉ ((syn_wne (.cv x) (syn_c0))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_n_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x n dv_cache_0001
  have p0001 :=
    @g_r19_41v (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (.cv x) (syn_c0)) n (syn_cnnc) dv_cache_0002
  have p0002 :=
    @g_neeq1 (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)
  have p0003 :=
    @g_pm5_32i (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0002
  have p0004 :=
    @g_rexbii (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (.cv x) (syn_c0))) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))) n (syn_cnnc) p0003
  have p0005 :=
    @g_bitr3i (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (.cv x) (syn_c0)))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) p0001 p0004
  have p0006 :=
    @g_abbii (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0))) (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))) x p0005
  have p0007 :=
    @g_eqtri (syn_coddfin) (.cab x (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne (.cv x) (syn_c0)))) (.cab x (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))) p0000 p0006
  exact p0007

#print axioms g_dfoddfin2

end NFChoice.DirectNominalPrf.WPPReplay
