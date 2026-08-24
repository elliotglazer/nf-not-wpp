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
import NominalWPPReplayChunk010Compact001Part026

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

noncomputable def g_vinf
     :
    Nominal.NPrf (.neg (.classMem (syn_cvv) (syn_cfin))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_noel (syn_cncfin (syn_cspfin))
  have p0001 :=
    @g_spfinex
  have p0002 :=
    @g_ncfinprop (syn_cspfin) (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cspfin) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin)))) p0001 p0002
  have p0004 :=
    @g_ne0i (syn_cncfin (syn_cspfin)) (syn_cspfin)
  have p0005 :=
    @g_anim2i (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin))) (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) p0004
  have p0006 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin)))) (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0))) p0003 p0005
  have p0007 :=
    @g_eldifsn (syn_cncfin (syn_cspfin)) (syn_cnnc) (syn_c0)
  have p0008 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin)) (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0))) (.classMem (syn_cncfin (syn_cspfin)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0006 p0007
  have p0009 :=
    @g_evenoddnnnul
  have p0010 :=
    @g_syl6eleqr (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cspfin)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cun (syn_cevenfin) (syn_coddfin)) p0008 p0009
  have p0011 :=
    @g_vfinncsp
  have p0012 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c))) (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) p0011
  have p0013 :=
    @g_eventfin (syn_cncfin (syn_cspfin))
  have p0014 :=
    @g_adantl (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cevenfin)) (.classMem (syn_cvv) (syn_cfin)) p0013
  have p0015 :=
    @g_evennnul (syn_cncfin (syn_cspfin))
  have p0016 :=
    @g_adantl (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0)) (.classMem (syn_cvv) (syn_cfin)) p0015
  have p0017 :=
    @g_eqnetrrd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))) (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_c0) p0012 p0016
  have p0018 :=
    @g_sucevenodd (syn_ctfin (syn_cncfin (syn_cspfin)))
  have p0019 :=
    @g_syl2anc (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))) (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cevenfin)) (syn_wne (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_c0)) (.classMem (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_coddfin)) p0014 p0017 p0018
  have p0020 :=
    @g_eqeltrd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))) (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_coddfin) p0012 p0019
  have p0021 :=
    @g_ex (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) p0020
  have p0022 :=
    @g_ancld (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) p0021
  have p0023 :=
    @g_vfinncsp
  have p0024 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c))) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) p0023
  have p0025 :=
    @g_oddtfin (syn_cncfin (syn_cspfin))
  have p0026 :=
    @g_adantl (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_coddfin)) (.classMem (syn_cvv) (syn_cfin)) p0025
  have p0027 :=
    @g_oddnnul (syn_cncfin (syn_cspfin))
  have p0028 :=
    @g_adantl (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0)) (.classMem (syn_cvv) (syn_cfin)) p0027
  have p0029 :=
    @g_eqnetrrd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))) (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_c0) p0024 p0028
  have p0030 :=
    @g_sucoddeven (syn_ctfin (syn_cncfin (syn_cspfin)))
  have p0031 :=
    @g_syl2anc (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))) (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_coddfin)) (syn_wne (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_c0)) (.classMem (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_cevenfin)) p0026 p0029 p0030
  have p0032 :=
    @g_eqeltrd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))) (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_cevenfin) p0024 p0031
  have p0033 :=
    @g_ex (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) p0032
  have p0034 :=
    @g_ancrd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) p0033
  have p0035 :=
    @g_jaod (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) p0022 p0034
  have p0036 :=
    @g_elun (syn_cncfin (syn_cspfin)) (syn_cevenfin) (syn_coddfin)
  have p0037 :=
    @g_elin (syn_cncfin (syn_cspfin)) (syn_cevenfin) (syn_coddfin)
  have p0038 :=
    @g_n_3imtr4g (.classMem (syn_cvv) (syn_cfin)) (syn_wo (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))) (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))) (.classMem (syn_cncfin (syn_cspfin)) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (syn_cncfin (syn_cspfin)) (syn_cin (syn_cevenfin) (syn_coddfin))) p0035 p0036 p0037
  have p0039 :=
    @g_mpd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cun (syn_cevenfin) (syn_coddfin))) (.classMem (syn_cncfin (syn_cspfin)) (syn_cin (syn_cevenfin) (syn_coddfin))) p0010 p0038
  have p0040 :=
    @g_evenodddisj
  have p0041 :=
    @g_syl6eleq (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cspfin)) (syn_cin (syn_cevenfin) (syn_coddfin)) (syn_c0) p0039 p0040
  have p0042 :=
    @g_mto (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_c0)) p0000 p0041
  exact p0042

noncomputable def g_nulnnn
     :
    Nominal.NPrf (.neg (.classMem (syn_c0) (syn_cnnc))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_ne_n : x ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have fresh_x_ne_m : x ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    Ne.symm fresh_x_ne_m
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_ne_a : n ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_n : a ≠ n :=
    Ne.symm fresh_n_ne_a
  have fresh_m_ne_a : m ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_m : a ≠ m :=
    Ne.symm fresh_m_ne_a
  have dv_cache_0001 : n ∉ ((syn_c0)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_ccompl (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_m, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((syn_wne (.cv m) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((syn_wne (.cv n) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((syn_wne (syn_c0c) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : n ∉ ((syn_wne (.cv x) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have dv_cache_0015 : x ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_complab (.classEq (.cv n) (syn_c0)) n
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn n (syn_c0) dv_cache_0001
  have p0002 :=
    @g_compleqi (syn_csn (syn_c0)) (.cab n (.classEq (.cv n) (syn_c0))) p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv n) (syn_c0))))
  have p0004 :=
    @g_abbii (syn_wne (.cv n) (syn_c0)) (.neg (.classEq (.cv n) (syn_c0))) n p0003
  have p0005 :=
    @g_n_3eqtr4ri (syn_ccompl (.cab n (.classEq (.cv n) (syn_c0)))) (.cab n (.neg (.classEq (.cv n) (syn_c0)))) (syn_ccompl (syn_csn (syn_c0))) (.cab n (syn_wne (.cv n) (syn_c0))) p0000 p0002 p0004
  have p0006 :=
    @g_snex (syn_c0)
  have p0007 :=
    @g_complex (syn_csn (syn_c0)) p0006
  have p0008 :=
    @g_eqeltri (.cab n (syn_wne (.cv n) (syn_c0))) (syn_ccompl (syn_csn (syn_c0))) (syn_cvv) p0005 p0007
  have p0009 :=
    @g_neeq1 (.cv n) (syn_c0c) (syn_c0)
  have p0010 :=
    @g_neeq1 (.cv n) (.cv m) (syn_c0)
  have p0011 :=
    @g_neeq1 (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_c0)
  have p0012 :=
    @g_neeq1 (.cv n) (.cv x) (syn_c0)
  have p0013 :=
    @g_nulel0c
  have p0014 :=
    @g_ne0i (syn_c0c) (syn_c0)
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_n0 a (.cv m) dv_cache_0002
  have p0017 :=
    @g_vinf
  have p0018 :=
    @g_elunii (syn_cvv) (.cv m) (syn_cnnc)
  have p0019 :=
    @g_ancoms (.classMem (syn_cvv) (.cv m)) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cvv) (syn_cuni (syn_cnnc))) p0018
  have p0020 :=
    (by simpa [syn_cfin] using (Nominal.classEqRefl (syn_cfin)))
  have p0021 :=
    @g_syl6eleqr (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cvv) (.cv m))) (syn_cvv) (syn_cuni (syn_cnnc)) (syn_cfin) p0019 p0020
  have p0022 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cvv) (.cv m)) (.classMem (syn_cvv) (syn_cfin)) p0021
  have p0023 :=
    @g_mtoi (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cvv) (.cv m)) (.classMem (syn_cvv) (syn_cfin)) p0017 p0022
  have p0024 :=
    @g_eleq1 (.cv a) (syn_cvv) (.cv m)
  have p0025_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (syn_cvv)) (syn_wb (.objMem a m) (.classMem (syn_cvv) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cvv syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0024
  have p0025 :=
    @g_notbid (.classEq (.cv a) (syn_cvv)) (.objMem a m) (.classMem (syn_cvv) (.cv m)) p0025_e00_recanon
  have p0026 :=
    @g_syl5ibrcom (.classMem (.cv m) (syn_cnnc)) (.neg (.objMem a m)) (.classEq (.cv a) (syn_cvv)) (.neg (.classMem (syn_cvv) (.cv m))) p0023 p0025
  have p0027 :=
    @g_necon2ad (.classMem (.cv m) (syn_cnnc)) (.objMem a m) (.cv a) (syn_cvv) p0026
  have p0028 :=
    @g_imp (.classMem (.cv m) (syn_cnnc)) (.objMem a m) (syn_wne (.cv a) (syn_cvv)) p0027
  have p0029 :=
    @g_compleqb (.cv a) (syn_cvv)
  have p0030 :=
    @g_necon3bii (.cv a) (syn_cvv) (syn_ccompl (.cv a)) (syn_ccompl (syn_cvv)) p0029
  have p0031 :=
    @g_sylib (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m)) (syn_wne (.cv a) (syn_cvv)) (syn_wne (syn_ccompl (.cv a)) (syn_ccompl (syn_cvv))) p0028 p0030
  have p0032 :=
    @g_complV
  have p0033 :=
    @g_neeq2i (syn_ccompl (syn_cvv)) (syn_c0) (syn_ccompl (.cv a)) p0032
  have p0034 :=
    @g_sylib (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m)) (syn_wne (syn_ccompl (.cv a)) (syn_ccompl (syn_cvv))) (syn_wne (syn_ccompl (.cv a)) (syn_c0)) p0031 p0033
  have p0035 :=
    @g_n0 x (syn_ccompl (.cv a)) dv_cache_0003
  have p0036 :=
    @g_vex x
  have p0037 :=
    @g_elcompl (.cv x) (.cv a) p0036
  have p0038 :=
    @g_elsuci (.cv a) (.cv m) (.cv x) p0036
  have p0039 :=
    @g_ne0i (syn_cplc (.cv m) (syn_c1c)) (syn_cun (.cv a) (syn_csn (.cv x)))
  have p0040_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objMem a m) (.neg (.objMem x a))) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0038
  have p0040 :=
    @g_syl (syn_wa (.objMem a m) (.neg (.objMem x a))) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0040_e00_recanon p0039
  have p0041_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv a))) (.neg (.objMem x a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0037
  have p0041 :=
    @g_sylan2b (.classMem (.cv x) (syn_ccompl (.cv a))) (.objMem a m) (.neg (.objMem x a)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0041_e00_recanon p0040
  have p0042 :=
    @g_ex (.objMem a m) (.classMem (.cv x) (syn_ccompl (.cv a))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0041
  have p0043 :=
    @g_adantl (.objMem a m) (.imp (.classMem (.cv x) (syn_ccompl (.cv a))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))) (.classMem (.cv m) (syn_cnnc)) p0042
  have p0044 :=
    @g_exlimdv (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m)) (.classMem (.cv x) (syn_ccompl (.cv a))) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) x dv_cache_0004 dv_cache_0005 p0043
  have p0045 :=
    @g_syl5bi (syn_wne (syn_ccompl (.cv a)) (syn_c0)) (syn_wex x (.classMem (.cv x) (syn_ccompl (.cv a)))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0035 p0044
  have p0046 :=
    @g_mpd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m)) (syn_wne (syn_ccompl (.cv a)) (syn_c0)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0034 p0045
  have p0047 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.objMem a m) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0046
  have p0048 :=
    @g_exlimdv (.classMem (.cv m) (syn_cnnc)) (.objMem a m) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) a dv_cache_0006 dv_cache_0007 p0047
  have p0049_e00_recanon : Nominal.NPrf (syn_wb (syn_wne (.cv m) (syn_c0)) (syn_wex a (.objMem a m))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0049 :=
    @g_syl5bi (syn_wne (.cv m) (syn_c0)) (syn_wex a (.objMem a m)) (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0049_e00_recanon p0048
  have p0050_e02_recanon : Nominal.NPrf (.imp (.objEq n m) (syn_wb (syn_wne (.cv n) (syn_c0)) (syn_wne (.cv m) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0010
  have p0050 :=
    @g_finds (syn_wne (.cv n) (syn_c0)) (syn_wne (syn_c0c) (syn_c0)) (syn_wne (.cv m) (syn_c0)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_wne (.cv x) (syn_c0)) n m (.cv x) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0008 p0009 p0050_e02_recanon p0011 p0012 p0015 p0049
  have p0051 :=
    @g_neneqd (.classMem (.cv x) (syn_cnnc)) (.cv x) (syn_c0) p0050
  have p0052 :=
    @g_nrex (.classEq (.cv x) (syn_c0)) x (syn_cnnc) p0051
  have p0053 :=
    @g_risset x (syn_c0) (syn_cnnc) dv_cache_0015 dv_cache_0016
  have p0054 :=
    @g_mtbir (.classMem (syn_c0) (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classEq (.cv x) (syn_c0))) p0052 p0053
  exact p0054

noncomputable def g_peano4
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (.classEq M N)) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
  have p0001 :=
    @g_simp3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
  have p0002 :=
    @g_peano2 M
  have p0003 :=
    @g_nulnnn
  have p0004 :=
    @g_eleq1 (syn_cplc M (syn_c1c)) (syn_c0) (syn_cnnc)
  have p0005 :=
    @g_mtbiri (.classEq (syn_cplc M (syn_c1c)) (syn_c0)) (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc)) p0003 p0004
  have p0006 :=
    @g_necon2ai (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc)) (syn_cplc M (syn_c1c)) (syn_c0) p0005
  have p0007 :=
    @g_syl (.classMem M (syn_cnnc)) (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc)) (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)) p0002 p0006
  have p0008 :=
    @g_n_3ad2ant1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) p0007
  have p0009 :=
    @g_prepeano4 M N
  have p0010 :=
    @g_syl12anc (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)) (.classEq M N) p0000 p0001 p0008 p0009
  exact p0010

noncomputable def g_suc11nnc
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wb (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (.classEq M N))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  have p0000 :=
    @g_peano4 M N
  have p0001 :=
    @g_n_3expia (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (.classEq M N) p0000
  have p0002 :=
    @g_addceq1 M N (syn_c1c)
  have p0003 :=
    @g_impbid1 (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (.classEq M N) p0001 p0002
  exact p0003

noncomputable def g_addccan2
    (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wb (.classEq (syn_cplc M N) (syn_cplc M P)) (.classEq N P))) := by
  let proofSupport : Finset Var := P.fv ∪ M.fv ∪ N.fv
  have p0000 :=
    @g_nncaddccl M N
  have p0001 :=
    @g_nulnnn
  have p0002 :=
    @g_eleq1 (syn_cplc M N) (syn_c0) (syn_cnnc)
  have p0003 :=
    @g_mtbiri (.classEq (syn_cplc M N) (syn_c0)) (.classMem (syn_cplc M N) (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_necon2ai (.classMem (syn_cplc M N) (syn_cnnc)) (syn_cplc M N) (syn_c0) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (syn_cplc M N) (syn_cnnc)) (syn_wne (syn_cplc M N) (syn_c0)) p0000 p0004
  have p0006 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne (syn_cplc M N) (syn_c0)) (.classMem P (syn_cnnc)) p0005
  have p0007 :=
    @g_preaddccan2 P M N
  have p0008 :=
    @g_mpdan (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wne (syn_cplc M N) (syn_c0)) (syn_wb (.classEq (syn_cplc M N) (syn_cplc M P)) (.classEq N P)) p0006 p0007
  exact p0008

noncomputable def g_addccan1
    (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wb (.classEq (syn_cplc M P) (syn_cplc N P)) (.classEq M N))) := by
  let proofSupport : Finset Var := P.fv ∪ M.fv ∪ N.fv
  have p0000 :=
    @g_addccom M P
  have p0001 :=
    @g_addccom N P
  have p0002 :=
    @g_eqeq12i (syn_cplc M P) (syn_cplc P M) (syn_cplc N P) (syn_cplc P N) p0000 p0001
  have p0003 :=
    @g_addccan2 N P M
  have p0004 :=
    @g_n_3coml (.classMem P (syn_cnnc)) (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wb (.classEq (syn_cplc P M) (syn_cplc P N)) (.classEq M N)) p0003
  have p0005 :=
    @g_syl5bb (.classEq (syn_cplc M P) (syn_cplc N P)) (.classEq (syn_cplc P M) (syn_cplc P N)) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (.classEq M N) p0002 p0004
  exact p0005

#print axioms g_addccan1

end NFChoice.DirectNominalPrf.WPPReplay
