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
import NominalWPPReplayChunk013Compact001Part043

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

noncomputable def g_ovmuc
    (g : Var) (M : Class) (N : Class) (a : Var) (b : Var) (dv_M_a : a ∉ M.fv) (dv_M_b : b ∉ M.fv) (dv_N_a : a ∉ N.fv) (dv_N_b : b ∉ N.fv) (dv_N_g : g ∉ N.fv) (dv_a_b : a ≠ b) (dv_a_g : a ≠ g) (dv_b_g : b ≠ g) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classEq (syn_co M (syn_cmuc) N) (.cab a (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))))) := by
  let proofSupport : Finset Var := ({g} : Finset Var) ∪ M.fv ∪ N.fv ∪ ({a} : Finset Var) ∪ ({b} : Finset Var)
  let c : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_g : c ≠ g := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_c : g ≠ c :=
    Ne.symm fresh_c_ne_g
  have fresh_c_not_M : c ∉ M.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_N : c ∉ N.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_ne_a : c ≠ a := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_c : a ≠ c :=
    Ne.symm fresh_c_ne_a
  have fresh_c_ne_b : c ≠ b := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_c : b ≠ c :=
    Ne.symm fresh_c_ne_b
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_ne_g : m ≠ g := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_m : g ≠ m :=
    Ne.symm fresh_m_ne_g
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_ne_a : m ≠ a := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_m : a ≠ m :=
    Ne.symm fresh_m_ne_a
  have fresh_m_ne_b : m ≠ b := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_m : b ≠ m :=
    Ne.symm fresh_m_ne_b
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_ne_g : n ≠ g := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_n : g ≠ n :=
    Ne.symm fresh_n_ne_g
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_n : a ≠ n :=
    Ne.symm fresh_n_ne_a
  have fresh_n_ne_b : n ≠ b := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_n : b ≠ n :=
    Ne.symm fresh_n_ne_b
  have fresh_c_ne_m : c ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_c : m ≠ c :=
    Ne.symm fresh_c_ne_m
  have fresh_c_ne_n : c ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_c : n ≠ c :=
    Ne.symm fresh_c_ne_n
  have fresh_m_ne_n : m ≠ n := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_m : n ≠ m :=
    Ne.symm fresh_m_ne_n
  have dv_cache_0001 : b ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_b), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ ((syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((syn_cop (.cv b) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_b_g), (Ne.symm dv_a_g), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : g ∉ ((syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : g ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : c ∉ ((syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_g, fresh_c_ne_b, fresh_c_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : c ∉ ((syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_cop (.cv c) (syn_cop (.cv g) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_c, dv_a_g, dv_a_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_cop (.cv b) (.cv g))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_a_b, dv_a_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((syn_wbr (syn_cop (.cv b) (.cv g)) (syn_ccross) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_a_b, dv_a_g, fresh_a_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : c ∉ ((syn_cxp (.cv b) (.cv g))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : c ∉ ((syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_b, fresh_c_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_a, dv_M_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((Wff.classEq (.cv m) M)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, dv_M_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : g ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : b ∉ ((Wff.classEq (.cv n) N)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_n, dv_N_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((Wff.classEq (.cv n) N)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, dv_N_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show a ≠ b from (by exact dv_a_b))
  have dv_cache_0022 : a ≠ g := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show a ≠ g from (by exact dv_a_g))
  have dv_cache_0023 : a ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show a ≠ m from (by exact fresh_a_ne_m))
  have dv_cache_0024 : a ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show a ≠ n from (by exact fresh_a_ne_n))
  have dv_cache_0025 : b ≠ g := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show b ≠ g from (by exact dv_b_g))
  have dv_cache_0026 : b ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (show b ≠ m from (by exact fresh_b_ne_m))
  have dv_cache_0027 : b ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show b ≠ n from (by exact fresh_b_ne_n))
  have dv_cache_0028 : g ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show g ≠ m from (by exact fresh_g_ne_m))
  have dv_cache_0029 : g ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show g ≠ n from (by exact fresh_g_ne_n))
  have dv_cache_0030 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0031 : m ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : n ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : m ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : n ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : m ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : n ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : m ∉ ((Class.cab a (syn_wrex b M (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_M, fresh_m_ne_n, fresh_m_ne_a, fresh_m_ne_b, fresh_m_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : m ∉ ((Class.cab a (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_M, fresh_m_not_N, fresh_m_ne_a, fresh_m_ne_b, fresh_m_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : n ∉ ((Class.cab a (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_M, fresh_n_not_N, fresh_n_ne_a, fresh_n_ne_b, fresh_n_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elima b (.cv a) (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv b) (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (.cv a))))
  have p0002 :=
    @g_elima g (syn_cop (.cv b) (.cv a)) (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv g) (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cop (.cv b) (.cv a)))))
  have p0004 :=
    @g_elrn2 c (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))) (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))) dv_cache_0007 dv_cache_0008
  have p0005 :=
    @g_elin (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))
  have p0006 :=
    @g_vex a
  have p0007 :=
    @g_oqelins4 (.cv c) (.cv g) (.cv b) (.cv a) (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))) p0006
  have p0008 :=
    @g_elrn a (syn_cop (.cv c) (syn_cop (.cv g) (.cv b))) (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))) dv_cache_0009 dv_cache_0010
  have p0009 :=
    @g_trtxp (.cv a) (.cv c) (syn_cop (.cv g) (.cv b)) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))
  have p0010 :=
    @g_trtxp (.cv a) (.cv g) (.cv b) (syn_c2nd) (syn_c1st)
  have p0011 :=
    @g_ancom (syn_wbr (.cv a) (syn_c2nd) (.cv g)) (syn_wbr (.cv a) (syn_c1st) (.cv b))
  have p0012 :=
    @g_vex b
  have p0013 :=
    @g_vex g
  have p0014 :=
    @g_op1st2nd (.cv b) (.cv g) (.cv a) p0012 p0013
  have p0015 :=
    @g_n_3bitri (syn_wbr (.cv a) (syn_ctxp (syn_c2nd) (syn_c1st)) (syn_cop (.cv g) (.cv b))) (syn_wa (syn_wbr (.cv a) (syn_c2nd) (.cv g)) (syn_wbr (.cv a) (syn_c1st) (.cv b))) (syn_wa (syn_wbr (.cv a) (syn_c1st) (.cv b)) (syn_wbr (.cv a) (syn_c2nd) (.cv g))) (.classEq (.cv a) (syn_cop (.cv b) (.cv g))) p0010 p0011 p0014
  have p0016 :=
    @g_anbi2i (syn_wbr (.cv a) (syn_ctxp (syn_c2nd) (syn_c1st)) (syn_cop (.cv g) (.cv b))) (.classEq (.cv a) (syn_cop (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_ccross) (.cv c)) p0015
  have p0017 :=
    @g_ancom (syn_wbr (.cv a) (syn_ccross) (.cv c)) (.classEq (.cv a) (syn_cop (.cv b) (.cv g)))
  have p0018 :=
    @g_n_3bitri (syn_wbr (.cv a) (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))) (syn_cop (.cv c) (syn_cop (.cv g) (.cv b)))) (syn_wa (syn_wbr (.cv a) (syn_ccross) (.cv c)) (syn_wbr (.cv a) (syn_ctxp (syn_c2nd) (syn_c1st)) (syn_cop (.cv g) (.cv b)))) (syn_wa (syn_wbr (.cv a) (syn_ccross) (.cv c)) (.classEq (.cv a) (syn_cop (.cv b) (.cv g)))) (syn_wa (.classEq (.cv a) (syn_cop (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_ccross) (.cv c))) p0009 p0016 p0017
  have p0019 :=
    @g_exbii (syn_wbr (.cv a) (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))) (syn_cop (.cv c) (syn_cop (.cv g) (.cv b)))) (syn_wa (.classEq (.cv a) (syn_cop (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_ccross) (.cv c))) a p0018
  have p0020 :=
    @g_opex (.cv b) (.cv g) p0012 p0013
  have p0021 :=
    @g_breq1 (.cv a) (syn_cop (.cv b) (.cv g)) (.cv c) (syn_ccross)
  have p0022 :=
    @g_ceqsexv (syn_wbr (.cv a) (syn_ccross) (.cv c)) (syn_wbr (syn_cop (.cv b) (.cv g)) (syn_ccross) (.cv c)) a (syn_cop (.cv b) (.cv g)) dv_cache_0011 dv_cache_0012 p0020 p0021
  have p0023 :=
    @g_n_3bitri (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (.cv b))) (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_wex a (syn_wbr (.cv a) (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))) (syn_cop (.cv c) (syn_cop (.cv g) (.cv b))))) (syn_wex a (syn_wa (.classEq (.cv a) (syn_cop (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_ccross) (.cv c)))) (syn_wbr (syn_cop (.cv b) (.cv g)) (syn_ccross) (.cv c)) p0008 p0019 p0022
  have p0024 :=
    @g_brcross (.cv b) (.cv g) (.cv c) p0012 p0013
  have p0025 :=
    @g_n_3bitri (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))) (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (.cv b))) (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_wbr (syn_cop (.cv b) (.cv g)) (syn_ccross) (.cv c)) (.classEq (.cv c) (syn_cxp (.cv b) (.cv g))) p0007 p0023 p0024
  have p0026 :=
    @g_otelins2 (.cv c) (.cv g) (syn_cop (.cv b) (.cv a)) (syn_cins2 (syn_ccnv (syn_cen))) p0013
  have p0027 :=
    @g_otelins2 (.cv c) (.cv b) (.cv a) (syn_ccnv (syn_cen)) p0012
  have p0028 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv c) (syn_ccnv (syn_cen)) (.cv a))))
  have p0029 :=
    @g_brcnv (.cv c) (.cv a) (syn_cen)
  have p0030 :=
    @g_bitr3i (.classMem (syn_cop (.cv c) (.cv a)) (syn_ccnv (syn_cen))) (syn_wbr (.cv c) (syn_ccnv (syn_cen)) (.cv a)) (syn_wbr (.cv a) (syn_cen) (.cv c)) p0028 p0029
  have p0031 :=
    @g_n_3bitri (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))) (.classMem (syn_cop (.cv c) (syn_cop (.cv b) (.cv a))) (syn_cins2 (syn_ccnv (syn_cen)))) (.classMem (syn_cop (.cv c) (.cv a)) (syn_ccnv (syn_cen))) (syn_wbr (.cv a) (syn_cen) (.cv c)) p0026 p0027 p0030
  have p0032 :=
    @g_anbi12i (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))) (.classEq (.cv c) (syn_cxp (.cv b) (.cv g))) (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))) (syn_wbr (.cv a) (syn_cen) (.cv c)) p0025 p0031
  have p0033 :=
    @g_bitri (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_wa (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))) (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_wa (.classEq (.cv c) (syn_cxp (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_cen) (.cv c))) p0005 p0032
  have p0034 :=
    @g_exbii (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_wa (.classEq (.cv c) (syn_cxp (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_cen) (.cv c))) c p0033
  have p0035 :=
    @g_xpex (.cv b) (.cv g) p0012 p0013
  have p0036 :=
    @g_breq2 (.cv c) (syn_cxp (.cv b) (.cv g)) (.cv a) (syn_cen)
  have p0037 :=
    @g_ceqsexv (syn_wbr (.cv a) (syn_cen) (.cv c)) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) c (syn_cxp (.cv b) (.cv g)) dv_cache_0013 dv_cache_0014 p0035 p0036
  have p0038 :=
    @g_n_3bitri (.classMem (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))) (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))) (syn_wex c (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))) (syn_wex c (syn_wa (.classEq (.cv c) (syn_cxp (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_cen) (.cv c)))) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) p0004 p0034 p0037
  have p0039 :=
    @g_bitri (syn_wbr (.cv g) (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cop (.cv b) (.cv a))) (.classMem (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))) (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) p0003 p0038
  have p0040 :=
    @g_rexbii (syn_wbr (.cv g) (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cop (.cv b) (.cv a))) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) g N p0039
  have p0041 :=
    @g_n_3bitri (syn_wbr (.cv b) (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (.cv a)) (.classMem (syn_cop (.cv b) (.cv a)) (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N)) (syn_wrex g N (syn_wbr (.cv g) (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cop (.cv b) (.cv a)))) (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))) p0001 p0002 p0040
  have p0042 :=
    @g_rexbii (syn_wbr (.cv b) (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (.cv a)) (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))) b M p0041
  have p0043 :=
    @g_bitri (.classMem (.cv a) (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M)) (syn_wrex b M (syn_wbr (.cv b) (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (.cv a))) (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))) p0000 p0042
  have p0044 :=
    @g_eqabi (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))) a (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M) dv_cache_0015 p0043
  have p0045 :=
    @g_crossex
  have p0046 :=
    @g_n_2ndex
  have p0047 :=
    @g_n_1stex
  have p0048 :=
    @g_txpex (syn_c2nd) (syn_c1st) p0046 p0047
  have p0049 :=
    @g_txpex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)) p0045 p0048
  have p0050 :=
    @g_rnex (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))) p0049
  have p0051 :=
    @g_ins4ex (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))) p0050
  have p0052 :=
    @g_enex
  have p0053 :=
    @g_cnvex (syn_cen) p0052
  have p0054 :=
    @g_ins2ex (syn_ccnv (syn_cen)) p0053
  have p0055 :=
    @g_ins2ex (syn_cins2 (syn_ccnv (syn_cen))) p0054
  have p0056 :=
    @g_inex (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))) p0051 p0055
  have p0057 :=
    @g_rnex (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))) p0056
  have p0058 :=
    @g_imaexg (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N (syn_cvv) (syn_cncs)
  have p0059 :=
    @g_mpan (.classMem (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cvv)) (.classMem N (syn_cncs)) (.classMem (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (syn_cvv)) p0057 p0058
  have p0060 :=
    @g_imaexg (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M (syn_cvv) (syn_cncs)
  have p0061 :=
    @g_sylan (.classMem N (syn_cncs)) (.classMem (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (syn_cvv)) (.classMem M (syn_cncs)) (.classMem (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M) (syn_cvv)) p0059 p0060
  have p0062 :=
    @g_ancoms (.classMem N (syn_cncs)) (.classMem M (syn_cncs)) (.classMem (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M) (syn_cvv)) p0061
  have p0063 :=
    @g_syl5eqelr (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.cab a (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))) (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M) (syn_cvv) p0044 p0062
  have p0064 :=
    @g_rexeq (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))) b (.cv m) M dv_cache_0016 dv_cache_0003
  have p0065 :=
    @g_abbidv (.classEq (.cv m) M) (syn_wrex b (.cv m) (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))) (syn_wrex b M (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))) a dv_cache_0017 p0064
  have p0066 :=
    @g_rexeq (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) g (.cv n) N dv_cache_0018 dv_cache_0006
  have p0067 :=
    @g_rexbidv (.classEq (.cv n) N) (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))) (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))) b M dv_cache_0019 p0066
  have p0068 :=
    @g_abbidv (.classEq (.cv n) N) (syn_wrex b M (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))) (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))) a dv_cache_0020 p0067
  have p0069 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_muc g m n a b dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
  have p0070 :=
    @g_ovmpt2g m n M N (syn_cncs) (syn_cncs) (.cab a (syn_wrex b (.cv m) (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))) (.cab a (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))) (syn_cmuc) (.cab a (syn_wrex b M (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))) (syn_cvv) dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0030 p0065 p0068 p0069
  have p0071 :=
    @g_mpd3an3 (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (.classMem (.cab a (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))) (syn_cvv)) (.classEq (syn_co M (syn_cmuc) N) (.cab a (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))) p0063 p0070
  exact p0071

#print axioms g_ovmuc

end NFChoice.DirectNominalPrf.WPPReplay
