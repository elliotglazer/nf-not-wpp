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
import NominalWPPReplayChunk013Compact001Part061

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

noncomputable def g_nncdiv3lem1
    (n : Var) (b : Var) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv n) (.cv b)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) := by
  let proofSupport : Finset Var := ({n} : Finset Var) ∪ ({b} : Finset Var)
  let m : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_m : n ≠ m :=
    Ne.symm fresh_m_ne_n
  have fresh_m_ne_b : m ≠ b := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_m : b ≠ m :=
    Ne.symm fresh_m_ne_b
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_t : n ≠ t :=
    Ne.symm fresh_t_ne_n
  have fresh_t_ne_b : t ≠ b := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_t : b ≠ t :=
    Ne.symm fresh_t_ne_b
  have fresh_m_ne_t : m ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_m : t ≠ m :=
    Ne.symm fresh_m_ne_t
  have dv_cache_0001 : m ∉ ((syn_cop (.cv n) (.cv b))).fv := by
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, fresh_m_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : m ∉ ((syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : m ∉ ((syn_cop (.cv t) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_t, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : m ∉ ((syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((syn_cproj1 (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : m ∉ ((syn_cop (.cv n) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_cop (.cv n) (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_n, fresh_t_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((syn_caddcfn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((syn_cop (syn_cop (.cv n) (.cv n)) (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_n, fresh_t_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((syn_cop (.cv m) (syn_cop (.cv n) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_m, fresh_t_ne_n, fresh_t_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : t ∉ ((syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : n ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : n ∉ ((syn_cproj1 (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : n ∉ ((syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_t, fresh_n_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : m ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : m ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : m ∉ ((syn_c2nd)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : m ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : m ∉ ((syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_t, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : t ∉ ((syn_cop (syn_cop (.cv m) (.cv n)) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_m, fresh_t_ne_n, fresh_t_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : m ∉ ((syn_cplc (.cv n) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : m ∉ ((Wff.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_b, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elrn2 m (syn_cop (.cv n) (.cv b)) (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elin (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))
  have p0002 :=
    @g_vex b
  have p0003 :=
    @g_otelins3 (.cv m) (.cv n) (.cv b) (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))) p0002
  have p0004 :=
    @g_opelcnv (.cv m) (.cv n) (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))
  have p0005 :=
    @g_trtxp (.cv t) (.cv n) (.cv m) (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)
  have p0006 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv t) (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (.cv n))))
  have p0007 :=
    @g_elrn2 m (syn_cop (.cv t) (.cv n)) (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))) dv_cache_0003 dv_cache_0004
  have p0008 :=
    @g_vex t
  have p0009 :=
    @g_proj1ex (.cv t) p0008
  have p0010 :=
    @g_eqvinc m (syn_cproj1 (.cv t)) (syn_cop (.cv n) (.cv n)) dv_cache_0005 dv_cache_0006 p0009
  have p0011 :=
    @g_opeq (.cv t)
  have p0012 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_cop (.cv n) (.cv n)) (syn_c1st) p0011
  have p0013 :=
    @g_proj2ex (.cv t) p0008
  have p0014 :=
    @g_opbr1st (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (syn_cop (.cv n) (.cv n)) p0009 p0013
  have p0015 :=
    @g_bitri (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n))) (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_c1st) (syn_cop (.cv n) (.cv n))) (.classEq (syn_cproj1 (.cv t)) (syn_cop (.cv n) (.cv n))) p0012 p0014
  have p0016 :=
    @g_oteltxp (.cv m) (.cv t) (.cv n) (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))
  have p0017 :=
    @g_opelcnv (.cv m) (.cv t) (syn_c1st)
  have p0018 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv t) (syn_c1st) (.cv m))))
  have p0019 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (.cv m) (syn_c1st) p0011
  have p0020 :=
    @g_opbr1st (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (.cv m) p0009 p0013
  have p0021 :=
    @g_eqcom (syn_cproj1 (.cv t)) (.cv m)
  have p0022 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_c1st) (.cv m)) (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_c1st) (.cv m)) (.classEq (syn_cproj1 (.cv t)) (.cv m)) (.classEq (.cv m) (syn_cproj1 (.cv t))) p0019 p0020 p0021
  have p0023 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv m) (.cv t)) (syn_ccnv (syn_c1st))) (.classMem (syn_cop (.cv t) (.cv m)) (syn_c1st)) (syn_wbr (.cv t) (syn_c1st) (.cv m)) (.classEq (.cv m) (syn_cproj1 (.cv t))) p0017 p0018 p0022
  have p0024 :=
    @g_elin (syn_cop (.cv m) (.cv n)) (syn_c1st) (syn_c2nd)
  have p0025 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv m) (syn_c1st) (.cv n))))
  have p0026 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv m) (syn_c2nd) (.cv n))))
  have p0027 :=
    @g_anbi12i (syn_wbr (.cv m) (syn_c1st) (.cv n)) (.classMem (syn_cop (.cv m) (.cv n)) (syn_c1st)) (syn_wbr (.cv m) (syn_c2nd) (.cv n)) (.classMem (syn_cop (.cv m) (.cv n)) (syn_c2nd)) p0025 p0026
  have p0028 :=
    @g_vex n
  have p0029 :=
    @g_op1st2nd (.cv n) (.cv n) (.cv m) p0028 p0028
  have p0030 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv m) (.cv n)) (syn_cin (syn_c1st) (syn_c2nd))) (syn_wa (.classMem (syn_cop (.cv m) (.cv n)) (syn_c1st)) (.classMem (syn_cop (.cv m) (.cv n)) (syn_c2nd))) (syn_wa (syn_wbr (.cv m) (syn_c1st) (.cv n)) (syn_wbr (.cv m) (syn_c2nd) (.cv n))) (.classEq (.cv m) (syn_cop (.cv n) (.cv n))) p0024 p0027 p0029
  have p0031 :=
    @g_anbi12i (.classMem (syn_cop (.cv m) (.cv t)) (syn_ccnv (syn_c1st))) (.classEq (.cv m) (syn_cproj1 (.cv t))) (.classMem (syn_cop (.cv m) (.cv n)) (syn_cin (syn_c1st) (syn_c2nd))) (.classEq (.cv m) (syn_cop (.cv n) (.cv n))) p0023 p0030
  have p0032 :=
    @g_bitri (.classMem (syn_cop (.cv m) (syn_cop (.cv t) (.cv n))) (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_wa (.classMem (syn_cop (.cv m) (.cv t)) (syn_ccnv (syn_c1st))) (.classMem (syn_cop (.cv m) (.cv n)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t))) (.classEq (.cv m) (syn_cop (.cv n) (.cv n)))) p0016 p0031
  have p0033 :=
    @g_exbii (.classMem (syn_cop (.cv m) (syn_cop (.cv t) (.cv n))) (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t))) (.classEq (.cv m) (syn_cop (.cv n) (.cv n)))) m p0032
  have p0034 :=
    @g_n_3bitr4ri (.classEq (syn_cproj1 (.cv t)) (syn_cop (.cv n) (.cv n))) (syn_wex m (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t))) (.classEq (.cv m) (syn_cop (.cv n) (.cv n))))) (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n))) (syn_wex m (.classMem (syn_cop (.cv m) (syn_cop (.cv t) (.cv n))) (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))) p0010 p0015 p0033
  have p0035 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (.cv n)) (.classMem (syn_cop (.cv t) (.cv n)) (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))) (syn_wex m (.classMem (syn_cop (.cv m) (syn_cop (.cv t) (.cv n))) (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))) (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n))) p0006 p0007 p0034
  have p0036 :=
    @g_anbi1i (syn_wbr (.cv t) (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (.cv n)) (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n))) (syn_wbr (.cv t) (syn_c2nd) (.cv m)) p0035
  have p0037 :=
    @g_opex (.cv n) (.cv n) p0028 p0028
  have p0038 :=
    @g_vex m
  have p0039 :=
    @g_op1st2nd (syn_cop (.cv n) (.cv n)) (.cv m) (.cv t) p0037 p0038
  have p0040 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_cop (.cv n) (.cv m))) (syn_wa (syn_wbr (.cv t) (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (.cv n)) (syn_wbr (.cv t) (syn_c2nd) (.cv m))) (syn_wa (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n))) (syn_wbr (.cv t) (syn_c2nd) (.cv m))) (.classEq (.cv t) (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m))) p0005 p0036 p0039
  have p0041 :=
    @g_rexbii (syn_wbr (.cv t) (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_cop (.cv n) (.cv m))) (.classEq (.cv t) (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m))) t (syn_caddcfn) p0040
  have p0042 :=
    @g_elima t (syn_cop (.cv n) (.cv m)) (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn) dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0043 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cop (.cv n) (.cv n)) (syn_caddcfn) (.cv m))))
  have p0044 :=
    @g_risset t (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m)) (syn_caddcfn) dv_cache_0010 dv_cache_0009
  have p0045 :=
    @g_bitri (syn_wbr (syn_cop (.cv n) (.cv n)) (syn_caddcfn) (.cv m)) (.classMem (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m)) (syn_caddcfn)) (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m)))) p0043 p0044
  have p0046 :=
    @g_n_3bitr4i (syn_wrex t (syn_caddcfn) (syn_wbr (.cv t) (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_cop (.cv n) (.cv m)))) (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m)))) (.classMem (syn_cop (.cv n) (.cv m)) (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))) (syn_wbr (syn_cop (.cv n) (.cv n)) (syn_caddcfn) (.cv m)) p0041 p0042 p0045
  have p0047 :=
    @g_braddcfn (.cv n) (.cv n) (.cv m) p0028 p0028
  have p0048 :=
    @g_eqcom (syn_cplc (.cv n) (.cv n)) (.cv m)
  have p0049 :=
    @g_n_3bitri (.classMem (syn_cop (.cv n) (.cv m)) (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))) (syn_wbr (syn_cop (.cv n) (.cv n)) (syn_caddcfn) (.cv m)) (.classEq (syn_cplc (.cv n) (.cv n)) (.cv m)) (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) p0046 p0047 p0048
  have p0050 :=
    @g_n_3bitri (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))) (.classMem (syn_cop (.cv m) (.cv n)) (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (.classMem (syn_cop (.cv n) (.cv m)) (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))) (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) p0003 p0004 p0049
  have p0051 :=
    @g_elima t (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn) dv_cache_0011 dv_cache_0012 dv_cache_0009
  have p0052 :=
    @g_trtxp (.cv t) (.cv m) (syn_cop (.cv n) (.cv b)) (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))
  have p0053 :=
    @g_trtxp (.cv t) (.cv n) (.cv b) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)
  have p0054 :=
    @g_anbi2i (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) (syn_cop (.cv n) (.cv b))) (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n)) (syn_wbr (.cv t) (syn_c2nd) (.cv b))) (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) p0053
  have p0055 :=
    @g_anass (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n)) (syn_wbr (.cv t) (syn_c2nd) (.cv b))
  have p0056 :=
    @g_op1st2nd (.cv m) (.cv n) (syn_cproj1 (.cv t)) p0038 p0028
  have p0057 :=
    @g_brco n (.cv t) (.cv m) (syn_c1st) (syn_c1st) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0015
  have p0058 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (.cv n) (syn_c1st) p0011
  have p0059 :=
    @g_opbr1st (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (.cv n) p0009 p0013
  have p0060 :=
    @g_eqcom (syn_cproj1 (.cv t)) (.cv n)
  have p0061 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_c1st) (.cv n)) (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_c1st) (.cv n)) (.classEq (syn_cproj1 (.cv t)) (.cv n)) (.classEq (.cv n) (syn_cproj1 (.cv t))) p0058 p0059 p0060
  have p0062 :=
    @g_anbi1i (syn_wbr (.cv t) (syn_c1st) (.cv n)) (.classEq (.cv n) (syn_cproj1 (.cv t))) (syn_wbr (.cv n) (syn_c1st) (.cv m)) p0061
  have p0063 :=
    @g_exbii (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv n)) (syn_wbr (.cv n) (syn_c1st) (.cv m))) (syn_wa (.classEq (.cv n) (syn_cproj1 (.cv t))) (syn_wbr (.cv n) (syn_c1st) (.cv m))) n p0062
  have p0064 :=
    @g_breq1 (.cv n) (syn_cproj1 (.cv t)) (.cv m) (syn_c1st)
  have p0065 :=
    @g_ceqsexv (syn_wbr (.cv n) (syn_c1st) (.cv m)) (syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m)) n (syn_cproj1 (.cv t)) dv_cache_0016 dv_cache_0017 p0009 p0064
  have p0066 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) (syn_wex n (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv n)) (syn_wbr (.cv n) (syn_c1st) (.cv m)))) (syn_wex n (syn_wa (.classEq (.cv n) (syn_cproj1 (.cv t))) (syn_wbr (.cv n) (syn_c1st) (.cv m)))) (syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m)) p0057 p0063 p0065
  have p0067 :=
    @g_brco m (.cv t) (.cv n) (syn_c2nd) (syn_c1st) dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0068 :=
    @g_anbi1i (syn_wbr (.cv t) (syn_c1st) (.cv m)) (.classEq (.cv m) (syn_cproj1 (.cv t))) (syn_wbr (.cv m) (syn_c2nd) (.cv n)) p0022
  have p0069 :=
    @g_exbii (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv m)) (syn_wbr (.cv m) (syn_c2nd) (.cv n))) (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t))) (syn_wbr (.cv m) (syn_c2nd) (.cv n))) m p0068
  have p0070 :=
    @g_breq1 (.cv m) (syn_cproj1 (.cv t)) (.cv n) (syn_c2nd)
  have p0071 :=
    @g_ceqsexv (syn_wbr (.cv m) (syn_c2nd) (.cv n)) (syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n)) m (syn_cproj1 (.cv t)) dv_cache_0005 dv_cache_0022 p0009 p0070
  have p0072 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n)) (syn_wex m (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv m)) (syn_wbr (.cv m) (syn_c2nd) (.cv n)))) (syn_wex m (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t))) (syn_wbr (.cv m) (syn_c2nd) (.cv n)))) (syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n)) p0067 p0069 p0071
  have p0073 :=
    @g_anbi12i (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) (syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m)) (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n)) (syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n)) p0066 p0072
  have p0074 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_cop (.cv m) (.cv n)) (syn_c1st) p0011
  have p0075 :=
    @g_opbr1st (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (syn_cop (.cv m) (.cv n)) p0009 p0013
  have p0076 :=
    @g_bitri (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n))) (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_c1st) (syn_cop (.cv m) (.cv n))) (.classEq (syn_cproj1 (.cv t)) (syn_cop (.cv m) (.cv n))) p0074 p0075
  have p0077 :=
    @g_n_3bitr4i (syn_wa (syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m)) (syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n))) (.classEq (syn_cproj1 (.cv t)) (syn_cop (.cv m) (.cv n))) (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n))) (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n))) p0056 p0073 p0076
  have p0078 :=
    @g_anbi1i (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n))) (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n))) (syn_wbr (.cv t) (syn_c2nd) (.cv b)) p0077
  have p0079 :=
    @g_n_3bitr2i (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) (syn_cop (.cv n) (.cv b)))) (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n)) (syn_wbr (.cv t) (syn_c2nd) (.cv b)))) (syn_wa (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n))) (syn_wbr (.cv t) (syn_c2nd) (.cv b))) (syn_wa (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n))) (syn_wbr (.cv t) (syn_c2nd) (.cv b))) p0054 p0055 p0078
  have p0080 :=
    @g_opex (.cv m) (.cv n) p0038 p0028
  have p0081 :=
    @g_op1st2nd (syn_cop (.cv m) (.cv n)) (.cv b) (.cv t) p0080 p0002
  have p0082 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_cop (.cv m) (syn_cop (.cv n) (.cv b)))) (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) (syn_cop (.cv n) (.cv b)))) (syn_wa (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n))) (syn_wbr (.cv t) (syn_c2nd) (.cv b))) (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b))) p0052 p0079 p0081
  have p0083 :=
    @g_rexbii (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_cop (.cv m) (syn_cop (.cv n) (.cv b)))) (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b))) t (syn_caddcfn) p0082
  have p0084 :=
    @g_bitri (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))) (syn_wrex t (syn_caddcfn) (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))))) (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b)))) p0051 p0083
  have p0085 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cop (.cv m) (.cv n)) (syn_caddcfn) (.cv b))))
  have p0086 :=
    @g_risset t (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b)) (syn_caddcfn) dv_cache_0023 dv_cache_0009
  have p0087 :=
    @g_bitr2i (syn_wbr (syn_cop (.cv m) (.cv n)) (syn_caddcfn) (.cv b)) (.classMem (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b)) (syn_caddcfn)) (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b)))) p0085 p0086
  have p0088 :=
    @g_braddcfn (.cv m) (.cv n) (.cv b) p0038 p0028
  have p0089 :=
    @g_eqcom (syn_cplc (.cv m) (.cv n)) (.cv b)
  have p0090 :=
    @g_bitri (syn_wbr (syn_cop (.cv m) (.cv n)) (syn_caddcfn) (.cv b)) (.classEq (syn_cplc (.cv m) (.cv n)) (.cv b)) (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))) p0088 p0089
  have p0091 :=
    @g_n_3bitri (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))) (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b)))) (syn_wbr (syn_cop (.cv m) (.cv n)) (syn_caddcfn) (.cv b)) (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))) p0084 p0087 p0090
  have p0092 :=
    @g_anbi12i (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))) (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))) (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))) p0050 p0091
  have p0093 :=
    @g_bitri (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_wa (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))) (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_wa (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) (.classEq (.cv b) (syn_cplc (.cv m) (.cv n)))) p0001 p0092
  have p0094 :=
    @g_exbii (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))) (syn_wa (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) (.classEq (.cv b) (syn_cplc (.cv m) (.cv n)))) m p0093
  have p0095 :=
    @g_addcex (.cv n) (.cv n) p0028 p0028
  have p0096 :=
    @g_addceq1 (.cv m) (syn_cplc (.cv n) (.cv n)) (.cv n)
  have p0097 :=
    @g_eqeq2d (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv n)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (.cv b) p0096
  have p0098 :=
    @g_ceqsexv (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))) (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) m (syn_cplc (.cv n) (.cv n)) dv_cache_0024 dv_cache_0025 p0095 p0097
  have p0099 :=
    @g_n_3bitri (.classMem (syn_cop (.cv n) (.cv b)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_wex m (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn)))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))) (syn_wex m (syn_wa (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))))) (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) p0000 p0094 p0098
  exact p0099

#print axioms g_nncdiv3lem1

end NFChoice.DirectNominalPrf.WPPReplay
