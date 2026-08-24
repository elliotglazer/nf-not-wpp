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
import NominalWPPReplayChunk013Compact001Part062

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

noncomputable def g_nncdiv3lem2
    (n : Var) (a : Var) (dv_a_n : a ≠ n) :
    Nominal.NPrf (.classMem (.cab a (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))) (syn_cvv)) := by
  let proofSupport : Finset Var := ({n} : Finset Var) ∪ ({a} : Finset Var)
  let b : Var := freshVar proofSupport 0
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_b : n ≠ b :=
    Ne.symm fresh_b_ne_n
  have fresh_b_ne_a : b ≠ a := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_b : a ≠ b :=
    Ne.symm fresh_b_ne_a
  have dv_cache_0001 : n ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((syn_cop (.cv n) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_n, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((syn_cop (.cv b) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, (Ne.symm dv_a_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((syn_cop (.cv b) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((syn_wbr (syn_cop (.cv b) (syn_c1c)) (syn_caddcfn) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, (Ne.symm dv_a_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : b ∉ ((syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((Wff.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((syn_cop (.cv b) (syn_c2c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : n ∉ ((syn_wbr (syn_cop (.cv b) (syn_c2c)) (syn_caddcfn) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, (Ne.symm dv_a_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ ((Wff.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((syn_cima (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elima n (.cv a) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv n) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (.cv a))))
  have p0002 :=
    @g_elun (syn_cop (.cv n) (.cv a)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))
  have p0003 :=
    @g_nncdiv3lem1 n a
  have p0004 :=
    @g_elrn2 b (syn_cop (.cv n) (.cv a)) (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))) dv_cache_0004 dv_cache_0005
  have p0005 :=
    @g_oteltxp (.cv b) (.cv n) (.cv a) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))
  have p0006 :=
    @g_opelcnv (.cv b) (.cv n) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
  have p0007 :=
    @g_nncdiv3lem1 n b
  have p0008 :=
    @g_bitri (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))) (.classMem (syn_cop (.cv n) (.cv b)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) p0006 p0007
  have p0009 :=
    @g_elrn2 n (syn_cop (.cv b) (.cv a)) (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)) dv_cache_0006 dv_cache_0007
  have p0010 :=
    @g_oteltxp (.cv n) (.cv b) (.cv a) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)
  have p0011 :=
    @g_elin (syn_cop (.cv n) (.cv b)) (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))
  have p0012 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv n) (syn_c1st) (.cv b))))
  have p0013 :=
    @g_bicomi (syn_wbr (.cv n) (syn_c1st) (.cv b)) (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st)) p0012
  have p0014 :=
    @g_vex b
  have p0015 :=
    @g_opelxp (.cv n) (.cv b) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)
  have p0016 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv n) (.cv b)) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (.classMem (.cv n) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))) (.classMem (.cv b) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_eliniseg (syn_c2nd) (syn_c1c) (.cv n)
  have p0018 :=
    @g_bitri (.classMem (syn_cop (.cv n) (.cv b)) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (.classMem (.cv n) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))) (syn_wbr (.cv n) (syn_c2nd) (syn_c1c)) p0016 p0017
  have p0019 :=
    @g_anbi12i (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st)) (syn_wbr (.cv n) (syn_c1st) (.cv b)) (.classMem (syn_cop (.cv n) (.cv b)) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_wbr (.cv n) (syn_c2nd) (syn_c1c)) p0013 p0018
  have p0020 :=
    @g_n_1cex
  have p0021 :=
    @g_op1st2nd (.cv b) (syn_c1c) (.cv n) p0014 p0020
  have p0022 :=
    @g_n_3bitri (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))) (syn_wa (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st)) (.classMem (syn_cop (.cv n) (.cv b)) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))) (syn_wa (syn_wbr (.cv n) (syn_c1st) (.cv b)) (syn_wbr (.cv n) (syn_c2nd) (syn_c1c))) (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c))) p0011 p0019 p0021
  have p0023 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv n) (syn_caddcfn) (.cv a))))
  have p0024 :=
    @g_bicomi (syn_wbr (.cv n) (syn_caddcfn) (.cv a)) (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn)) p0023
  have p0025 :=
    @g_anbi12i (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))) (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn)) (syn_wbr (.cv n) (syn_caddcfn) (.cv a)) p0022 p0024
  have p0026 :=
    @g_bitri (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))) (syn_wa (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn))) (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c))) (syn_wbr (.cv n) (syn_caddcfn) (.cv a))) p0010 p0025
  have p0027 :=
    @g_exbii (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))) (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c))) (syn_wbr (.cv n) (syn_caddcfn) (.cv a))) n p0026
  have p0028 :=
    @g_bitri (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))) (syn_wex n (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))) (syn_wex n (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c))) (syn_wbr (.cv n) (syn_caddcfn) (.cv a)))) p0009 p0027
  have p0029 :=
    @g_n_1cex
  have p0030 :=
    @g_opex (.cv b) (syn_c1c) p0014 p0029
  have p0031 :=
    @g_breq1 (.cv n) (syn_cop (.cv b) (syn_c1c)) (.cv a) (syn_caddcfn)
  have p0032 :=
    @g_ceqsexv (syn_wbr (.cv n) (syn_caddcfn) (.cv a)) (syn_wbr (syn_cop (.cv b) (syn_c1c)) (syn_caddcfn) (.cv a)) n (syn_cop (.cv b) (syn_c1c)) dv_cache_0008 dv_cache_0009 p0030 p0031
  have p0033 :=
    @g_n_1cex
  have p0034 :=
    @g_braddcfn (.cv b) (syn_c1c) (.cv a) p0014 p0033
  have p0035 :=
    @g_eqcom (syn_cplc (.cv b) (syn_c1c)) (.cv a)
  have p0036 :=
    @g_bitri (syn_wbr (syn_cop (.cv b) (syn_c1c)) (syn_caddcfn) (.cv a)) (.classEq (syn_cplc (.cv b) (syn_c1c)) (.cv a)) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))) p0034 p0035
  have p0037 :=
    @g_n_3bitri (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))) (syn_wex n (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c))) (syn_wbr (.cv n) (syn_caddcfn) (.cv a)))) (syn_wbr (syn_cop (.cv b) (syn_c1c)) (syn_caddcfn) (.cv a)) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))) p0028 p0032 p0036
  have p0038 :=
    @g_anbi12i (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))) (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))) p0008 p0037
  have p0039 :=
    @g_bitri (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))))) (syn_wa (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))) (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))))) (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c)))) p0005 p0038
  have p0040 :=
    @g_exbii (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))))) (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c)))) b p0039
  have p0041 :=
    @g_vex n
  have p0042 :=
    @g_addcex (.cv n) (.cv n) p0041 p0041
  have p0043 :=
    @g_addcex (syn_cplc (.cv n) (.cv n)) (.cv n) p0042 p0041
  have p0044 :=
    @g_addceq1 (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)
  have p0045 :=
    @g_eqeq2d (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_cplc (.cv b) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (.cv a) p0044
  have p0046 :=
    @g_ceqsexv (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) b (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) dv_cache_0010 dv_cache_0011 p0043 p0045
  have p0047 :=
    @g_n_3bitri (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_wex b (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_wex b (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) p0004 p0040 p0046
  have p0048 :=
    @g_orbi12i (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) p0003 p0047
  have p0049 :=
    @g_bitri (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))))))) (syn_wo (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))))))) (syn_wo (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) p0002 p0048
  have p0050 :=
    @g_elrn2 b (syn_cop (.cv n) (.cv a)) (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))) dv_cache_0004 dv_cache_0012
  have p0051 :=
    @g_oteltxp (.cv b) (.cv n) (.cv a) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))
  have p0052 :=
    @g_elrn2 n (syn_cop (.cv b) (.cv a)) (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)) dv_cache_0006 dv_cache_0013
  have p0053 :=
    @g_oteltxp (.cv n) (.cv b) (.cv a) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)
  have p0054 :=
    @g_elin (syn_cop (.cv n) (.cv b)) (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))
  have p0055 :=
    @g_opelxp (.cv n) (.cv b) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)
  have p0056 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv n) (.cv b)) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (.classMem (.cv n) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c)))) (.classMem (.cv b) (syn_cvv)) p0014 p0055
  have p0057 :=
    @g_eliniseg (syn_c2nd) (syn_c2c) (.cv n)
  have p0058 :=
    @g_bitri (.classMem (syn_cop (.cv n) (.cv b)) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (.classMem (.cv n) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c)))) (syn_wbr (.cv n) (syn_c2nd) (syn_c2c)) p0056 p0057
  have p0059 :=
    @g_anbi12i (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st)) (syn_wbr (.cv n) (syn_c1st) (.cv b)) (.classMem (syn_cop (.cv n) (.cv b)) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_wbr (.cv n) (syn_c2nd) (syn_c2c)) p0013 p0058
  have p0060 :=
    (by simpa [syn_c2c] using (Nominal.classEqRefl (syn_c2c)))
  have p0061 :=
    @g_ncex (syn_cpr (syn_c0) (syn_cvv))
  have p0062 :=
    @g_eqeltri (syn_c2c) (syn_cnc (syn_cpr (syn_c0) (syn_cvv))) (syn_cvv) p0060 p0061
  have p0063 :=
    @g_op1st2nd (.cv b) (syn_c2c) (.cv n) p0014 p0062
  have p0064 :=
    @g_n_3bitri (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))) (syn_wa (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st)) (.classMem (syn_cop (.cv n) (.cv b)) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))) (syn_wa (syn_wbr (.cv n) (syn_c1st) (.cv b)) (syn_wbr (.cv n) (syn_c2nd) (syn_c2c))) (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c))) p0054 p0059 p0063
  have p0065 :=
    @g_anbi12i (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))) (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn)) (syn_wbr (.cv n) (syn_caddcfn) (.cv a)) p0064 p0024
  have p0066 :=
    @g_bitri (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))) (syn_wa (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn))) (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c))) (syn_wbr (.cv n) (syn_caddcfn) (.cv a))) p0053 p0065
  have p0067 :=
    @g_exbii (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))) (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c))) (syn_wbr (.cv n) (syn_caddcfn) (.cv a))) n p0066
  have p0068 :=
    @g_opex (.cv b) (syn_c2c) p0014 p0062
  have p0069 :=
    @g_breq1 (.cv n) (syn_cop (.cv b) (syn_c2c)) (.cv a) (syn_caddcfn)
  have p0070 :=
    @g_ceqsexv (syn_wbr (.cv n) (syn_caddcfn) (.cv a)) (syn_wbr (syn_cop (.cv b) (syn_c2c)) (syn_caddcfn) (.cv a)) n (syn_cop (.cv b) (syn_c2c)) dv_cache_0014 dv_cache_0015 p0068 p0069
  have p0071 :=
    @g_n_3bitri (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))) (syn_wex n (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))) (syn_wex n (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c))) (syn_wbr (.cv n) (syn_caddcfn) (.cv a)))) (syn_wbr (syn_cop (.cv b) (syn_c2c)) (syn_caddcfn) (.cv a)) p0052 p0067 p0070
  have p0072 :=
    @g_braddcfn (.cv b) (syn_c2c) (.cv a) p0014 p0062
  have p0073 :=
    @g_eqcom (syn_cplc (.cv b) (syn_c2c)) (.cv a)
  have p0074 :=
    @g_n_3bitri (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))) (syn_wbr (syn_cop (.cv b) (syn_c2c)) (syn_caddcfn) (.cv a)) (.classEq (syn_cplc (.cv b) (syn_c2c)) (.cv a)) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c))) p0071 p0072 p0073
  have p0075 :=
    @g_anbi12i (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))) (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c))) p0008 p0074
  have p0076 :=
    @g_bitri (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))))) (syn_wa (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))) (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))))) (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c)))) p0051 p0075
  have p0077 :=
    @g_exbii (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))))) (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c)))) b p0076
  have p0078 :=
    @g_addceq1 (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)
  have p0079 :=
    @g_eqeq2d (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_cplc (.cv b) (syn_c2c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (.cv a) p0078
  have p0080 :=
    @g_ceqsexv (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) b (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) dv_cache_0010 dv_cache_0016 p0043 p0079
  have p0081 :=
    @g_n_3bitri (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (syn_wex b (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (syn_wex b (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c))))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0050 p0077 p0080
  have p0082 :=
    @g_orbi12i (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))))))) (syn_wo (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0049 p0081
  have p0083 :=
    @g_elun (syn_cop (.cv n) (.cv a)) (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))
  have p0084 :=
    (by simpa [syn_wb, syn_w3o] using (Nominal.biimpRefl (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))))
  have p0085 :=
    @g_n_3bitr4i (syn_wo (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))))))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))))))) (syn_wo (syn_wo (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))))))) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) p0082 p0083 p0084
  have p0086 :=
    @g_bitri (syn_wbr (.cv n) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (.cv a)) (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))))))) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) p0001 p0085
  have p0087 :=
    @g_rexbii (syn_wbr (.cv n) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (.cv a)) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))) n (syn_cnnc) p0086
  have p0088 :=
    @g_bitri (.classMem (.cv a) (syn_cima (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (syn_cnnc))) (syn_wrex n (syn_cnnc) (syn_wbr (.cv n) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (.cv a))) (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) p0000 p0087
  have p0089 :=
    @g_eqabi (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) a (syn_cima (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (syn_cnnc)) dv_cache_0017 p0088
  have p0090 :=
    @g_n_1stex
  have p0091 :=
    @g_cnvex (syn_c1st) p0090
  have p0092 :=
    @g_n_1stex
  have p0093 :=
    @g_n_2ndex
  have p0094 :=
    @g_inex (syn_c1st) (syn_c2nd) p0092 p0093
  have p0095 :=
    @g_txpex (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)) p0091 p0094
  have p0096 :=
    @g_rnex (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))) p0095
  have p0097 :=
    @g_n_2ndex
  have p0098 :=
    @g_txpex (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd) p0096 p0097
  have p0099 :=
    @g_addcfnex
  have p0100 :=
    @g_imaex (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn) p0098 p0099
  have p0101 :=
    @g_cnvex (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)) p0100
  have p0102 :=
    @g_ins3ex (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))) p0101
  have p0103 :=
    @g_n_1stex
  have p0104 :=
    @g_n_1stex
  have p0105 :=
    @g_coex (syn_c1st) (syn_c1st) p0103 p0104
  have p0106 :=
    @g_n_2ndex
  have p0107 :=
    @g_n_1stex
  have p0108 :=
    @g_coex (syn_c2nd) (syn_c1st) p0106 p0107
  have p0109 :=
    @g_n_2ndex
  have p0110 :=
    @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd) p0108 p0109
  have p0111 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) p0105 p0110
  have p0112 :=
    @g_addcfnex
  have p0113 :=
    @g_imaex (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn) p0111 p0112
  have p0114 :=
    @g_inex (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)) p0102 p0113
  have p0115 :=
    @g_rnex (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))) p0114
  have p0116 :=
    @g_cnvex (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) p0115
  have p0117 :=
    @g_n_1stex
  have p0118 :=
    @g_n_2ndex
  have p0119 :=
    @g_cnvex (syn_c2nd) p0118
  have p0120 :=
    @g_snex (syn_c1c)
  have p0121 :=
    @g_imaex (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)) p0119 p0120
  have p0122 :=
    @g_vvex
  have p0123 :=
    @g_xpex (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv) p0121 p0122
  have p0124 :=
    @g_inex (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)) p0117 p0123
  have p0125 :=
    @g_addcfnex
  have p0126 :=
    @g_txpex (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn) p0124 p0125
  have p0127 :=
    @g_rnex (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)) p0126
  have p0128 :=
    @g_txpex (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))) p0116 p0127
  have p0129 :=
    @g_rnex (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))) p0128
  have p0130 :=
    @g_unex (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn))))) p0115 p0129
  have p0131 :=
    @g_n_1stex
  have p0132 :=
    @g_snex (syn_c2c)
  have p0133 :=
    @g_imaex (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c)) p0119 p0132
  have p0134 :=
    @g_vvex
  have p0135 :=
    @g_xpex (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv) p0133 p0134
  have p0136 :=
    @g_inex (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)) p0131 p0135
  have p0137 :=
    @g_addcfnex
  have p0138 :=
    @g_txpex (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn) p0136 p0137
  have p0139 :=
    @g_rnex (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)) p0138
  have p0140 :=
    @g_txpex (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))) p0116 p0139
  have p0141 :=
    @g_rnex (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))) p0140
  have p0142 :=
    @g_unex (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn))))) p0130 p0141
  have p0143 :=
    @g_nncex
  have p0144 :=
    @g_imaex (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (syn_cnnc) p0142 p0143
  have p0145 :=
    @g_eqeltrri (syn_cima (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st) (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))) (syn_caddcfn)))))) (syn_cnnc)) (.cab a (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))) (syn_cvv) p0089 p0144
  exact p0145

#print axioms g_nncdiv3lem2

end NFChoice.DirectNominalPrf.WPPReplay
