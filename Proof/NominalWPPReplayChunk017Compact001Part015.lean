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
import NominalWPPReplayChunk017Compact001Part014

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

noncomputable def g_wppqkrelrescnvfunndv
    (A : Class) (B : Class) (hyp_wppqkrelrescnvfunndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_wppqkrelrescnvfunndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wfun (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let d : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  let u : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let b : Var := freshVar proofSupport 5
  let v : Var := freshVar proofSupport 6
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_d_ne_s : d ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_d : s ≠ d :=
    Ne.symm fresh_d_ne_s
  have fresh_d_ne_t : d ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_d : t ≠ d :=
    Ne.symm fresh_d_ne_t
  have fresh_d_ne_u : d ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_u_ne_d : u ≠ d :=
    Ne.symm fresh_d_ne_u
  have fresh_d_ne_a : d ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_d : a ≠ d :=
    Ne.symm fresh_d_ne_a
  have fresh_d_ne_b : d ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_b_ne_d : b ≠ d :=
    Ne.symm fresh_d_ne_b
  have fresh_d_ne_v : d ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_v_ne_d : v ≠ d :=
    Ne.symm fresh_d_ne_v
  have fresh_s_ne_t : s ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_s : t ≠ s :=
    Ne.symm fresh_s_ne_t
  have fresh_s_ne_u : s ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_u_ne_s : u ≠ s :=
    Ne.symm fresh_s_ne_u
  have fresh_s_ne_a : s ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_s : a ≠ s :=
    Ne.symm fresh_s_ne_a
  have fresh_s_ne_b : s ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_b_ne_s : b ≠ s :=
    Ne.symm fresh_s_ne_b
  have fresh_s_ne_v : s ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_v_ne_s : v ≠ s :=
    Ne.symm fresh_s_ne_v
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have fresh_t_ne_a : t ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_t : a ≠ t :=
    Ne.symm fresh_t_ne_a
  have fresh_t_ne_b : t ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_b_ne_t : b ≠ t :=
    Ne.symm fresh_t_ne_b
  have fresh_t_ne_v : t ≠ v := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_v_ne_t : v ≠ t :=
    Ne.symm fresh_t_ne_v
  have fresh_u_ne_a : u ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_u : a ≠ u :=
    Ne.symm fresh_u_ne_a
  have fresh_u_ne_b : u ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_b_ne_u : b ≠ u :=
    Ne.symm fresh_u_ne_b
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_v : a ≠ v := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_v_ne_a : v ≠ a :=
    Ne.symm fresh_a_ne_v
  have fresh_b_ne_v : b ≠ v := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_v_ne_b : v ≠ b :=
    Ne.symm fresh_b_ne_v
  have dv_cache_0001 : u ∉ ((Class.cv s)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0010 : a ∉ ((syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_d, fresh_a_ne_s, fresh_a_not_A, fresh_a_not_B, fresh_a_ne_t, fresh_a_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Wff.classEq (.cv s) (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_s, fresh_a_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_d, fresh_b_ne_s, fresh_b_not_A, fresh_b_not_B, fresh_b_ne_t, fresh_b_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ ((Wff.classEq (.cv s) (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_s, fresh_b_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : v ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : v ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, fresh_v_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : v ∉ ((Wff.classEq (.cv s) (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_s, fresh_v_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : v ∉ ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_d, fresh_v_ne_s, fresh_v_not_A, fresh_v_not_B, fresh_v_ne_t, fresh_v_ne_u, fresh_v_ne_a, fresh_v_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : u ∉ ((Wff.classEq (.cv s) (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_s, fresh_u_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : u ∉ ((syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_d, fresh_u_ne_s, fresh_u_not_A, fresh_u_not_B, fresh_u_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : d ∉ ((syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : s ∉ ((syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, fresh_s_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : t ∉ ((syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : d ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0024 : d ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show d ≠ t from (by exact fresh_d_ne_t))
  have dv_cache_0025 : s ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show s ≠ t from (by exact fresh_s_ne_t))
  have p0000 :=
    @g_simpl (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))
  have p0001 :=
    @g_brcnv (.cv d) (.cv s) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0002 :=
    @g_brres (.cv s) (.cv d) (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))
  have p0003 :=
    @g_bitri (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv s) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.cv d)) (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0001 p0002
  have p0004 :=
    @g_biimpi (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0003
  have p0005 :=
    @g_syl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0000 p0004
  have p0006 :=
    @g_simpr (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0007 :=
    @g_syl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) p0005 p0006
  have p0008 :=
    @g_elpw12 u (.cv s) (syn_cxp A B) dv_cache_0001 dv_cache_0002
  have p0009 :=
    @g_biimpi (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) p0007 p0009
  have p0011 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0012 :=
    @g_simpr (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classMem (.cv u) (syn_cxp A B)) p0011 p0012
  have p0014 :=
    @g_elxp a b (.cv u) A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0015 :=
    @g_biimpi (.classMem (.cv u) (syn_cxp A B)) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))) p0014
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (.classMem (.cv u) (syn_cxp A B)) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))) p0013 p0015
  have p0017 :=
    @g_nfv (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) a dv_cache_0010
  have p0018 :=
    @g_nfv (.classEq (.cv s) (.cv t)) a dv_cache_0011
  have p0019 :=
    @g_nfv (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) b dv_cache_0012
  have p0020 :=
    @g_nfv (.classEq (.cv s) (.cv t)) b dv_cache_0013
  have p0021 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0022 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0023 :=
    @g_simpl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) p0022 p0023
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) p0021 p0024
  have p0026 :=
    @g_simpr (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))
  have p0027 :=
    @g_brcnv (.cv d) (.cv t) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0028 :=
    @g_brres (.cv t) (.cv d) (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))
  have p0029 :=
    @g_bitri (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)) (syn_wbr (.cv t) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.cv d)) (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0027 p0028
  have p0030 :=
    @g_biimpi (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)) (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0029
  have p0031 :=
    @g_syl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)) (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0026 p0030
  have p0032 :=
    @g_simpr (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0033 :=
    @g_syl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) p0031 p0032
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) p0025 p0033
  have p0035 :=
    @g_elpw12 v (.cv t) (syn_cxp A B) dv_cache_0014 dv_cache_0015
  have p0036 :=
    @g_biimpi (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wrex v (syn_cxp A B) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) p0035
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wrex v (syn_cxp A B) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) p0034 p0036
  have p0038 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))
  have p0039 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) p0038 p0039
  have p0041 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0042 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) p0041 p0042
  have p0044 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0045 :=
    @g_simpl (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))) (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) p0044 p0045
  have p0047 :=
    @g_sneq (.cv u) (syn_cop (.cv a) (.cv b))
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (.classEq (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b)))) p0046 p0047
  have p0049 :=
    @g_sneqd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b))) p0048
  have p0050 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.cv s) (syn_csn (syn_csn (.cv u))) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) p0043 p0049
  have p0051 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classEq (.cv s) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b))))) p0040 p0050
  have p0052 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))
  have p0053 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))
  have p0054 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))
  have p0055 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) p0053 p0054
  have p0056 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0057 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0058 :=
    @g_simpl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))
  have p0059 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) p0057 p0058
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) p0056 p0059
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) p0055 p0060
  have p0062 :=
    @g_simpr (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))
  have p0063 :=
    @g_brcnv (.cv d) (.cv t) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0064 :=
    @g_brres (.cv t) (.cv d) (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))
  have p0065 :=
    @g_bitri (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)) (syn_wbr (.cv t) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.cv d)) (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0063 p0064
  have p0066 :=
    @g_biimpi (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)) (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0065
  have p0067 :=
    @g_syl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)) (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0062 p0066
  have p0068 :=
    @g_simpl (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0069 :=
    @g_syl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) p0067 p0068
  have p0070 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) p0061 p0069
  have p0071 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))))
  have p0072 :=
    @g_biimpi (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (syn_cop (.cv t) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0071
  have p0073 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (syn_cop (.cv t) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0070 p0072
  have p0074 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))
  have p0075 :=
    @g_opeq1d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.cv t) (syn_csn (syn_csn (.cv v))) (.cv d) p0074
  have p0076 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_cop (.cv t) (.cv d)) (syn_cop (syn_csn (syn_csn (.cv v))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)) p0075
  have p0077 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.classMem (syn_cop (.cv t) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0073 p0076
  have p0078 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))
  have p0079 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) p0078 p0079
  have p0081 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0082 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0083 :=
    @g_simpl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))
  have p0084 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) p0082 p0083
  have p0085 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) p0081 p0084
  have p0086 :=
    @g_simpl (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))
  have p0087 :=
    @g_brcnv (.cv d) (.cv s) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0088 :=
    @g_brres (.cv s) (.cv d) (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))
  have p0089 :=
    @g_bitri (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv s) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (.cv d)) (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0087 p0088
  have p0090 :=
    @g_biimpi (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0089
  have p0091 :=
    @g_syl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) p0086 p0090
  have p0092 :=
    @g_simpl (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0093 :=
    @g_syl (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) p0091 p0092
  have p0094 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) p0085 p0093
  have p0095 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))))
  have p0096 :=
    @g_biimpi (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0095
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0094 p0096
  have p0098 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0099 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0100 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) p0098 p0099
  have p0101 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0102 :=
    @g_simpl (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))
  have p0103 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))) (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) p0101 p0102
  have p0104 :=
    @g_sneq (.cv u) (syn_cop (.cv a) (.cv b))
  have p0105 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (.classEq (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b)))) p0103 p0104
  have p0106 :=
    @g_sneqd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b))) p0105
  have p0107 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.cv s) (syn_csn (syn_csn (.cv u))) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) p0100 p0106
  have p0108 :=
    @g_opeq1d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.cv s) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d) p0107
  have p0109 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_cop (.cv s) (.cv d)) (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)) p0108
  have p0110 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0097 p0109
  have p0111 :=
    @g_vex a
  have p0112 :=
    @g_vex b
  have p0113 :=
    @g_vex d
  have p0114 :=
    @g_wppqkrelcanonicalfiberndv (.cv a) (.cv b) (.cv d) p0111 p0112 p0113
  have p0115 :=
    @g_biimpi (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq (.cv d) (syn_copk (.cv a) (.cv b))) p0114
  have p0116 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq (.cv d) (syn_copk (.cv a) (.cv b))) p0110 p0115
  have p0117 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classEq (.cv d) (syn_copk (.cv a) (.cv b))) p0080 p0116
  have p0118 :=
    @g_opeq2d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.cv d) (syn_copk (.cv a) (.cv b)) (syn_csn (syn_csn (.cv v))) p0117
  have p0119 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_cop (syn_csn (syn_csn (.cv v))) (.cv d)) (syn_cop (syn_csn (syn_csn (.cv v))) (syn_copk (.cv a) (.cv b))) (syn_ckqrel (syn_cwppqkrelkernel)) p0118
  have p0120 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (syn_copk (.cv a) (.cv b))) (syn_ckqrel (syn_cwppqkrelkernel))) p0077 p0119
  have p0121 :=
    @g_vex v
  have p0122 :=
    @g_vex a
  have p0123 :=
    @g_vex b
  have p0124 :=
    @g_wppqkrelkernelpointbrndv (.cv v) (.cv a) (.cv b) p0121 p0122 p0123
  have p0125 :=
    @g_biimpi (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (syn_copk (.cv a) (.cv b))) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq (.cv v) (syn_cop (.cv a) (.cv b))) p0124
  have p0126 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (syn_copk (.cv a) (.cv b))) (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq (.cv v) (syn_cop (.cv a) (.cv b))) p0120 p0125
  have p0127 :=
    @g_sneqd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.cv v) (syn_cop (.cv a) (.cv b)) p0126
  have p0128 :=
    @g_sneqd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (syn_csn (.cv v)) (syn_csn (syn_cop (.cv a) (.cv b))) p0127
  have p0129 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.cv t) (syn_csn (syn_csn (.cv v))) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) p0052 p0128
  have p0130 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.cv t) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) p0129
  have p0131 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.cv s) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv t) p0051 p0130
  have p0132 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))) (.classEq (.cv s) (.cv t)) p0131
  have p0133 :=
    @g_rexlimdva (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))) (.classEq (.cv s) (.cv t)) v (syn_cxp A B) dv_cache_0016 dv_cache_0017 p0132
  have p0134 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (syn_wrex v (syn_cxp A B) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) (.classEq (.cv s) (.cv t)) p0037 p0133
  have p0135 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))) (.classEq (.cv s) (.cv t)) p0134
  have p0136 :=
    @g_exlimd (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))) (.classEq (.cv s) (.cv t)) b p0019 p0020 p0135
  have p0137 :=
    @g_exlimd (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))) (.classEq (.cv s) (.cv t)) a p0017 p0018 p0136
  have p0138 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))) (.classEq (.cv s) (.cv t)) p0016 p0137
  have p0139 :=
    @g_ex (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) (.classEq (.cv s) (.cv t)) p0138
  have p0140 :=
    @g_rexlimdva (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) (.classEq (.cv s) (.cv t)) u (syn_cxp A B) dv_cache_0018 dv_cache_0019 p0139
  have p0141 :=
    @g_mpd (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) (.classEq (.cv s) (.cv t)) p0010 p0140
  have p0142 :=
    Nominal.gen p0141 t
  have p0143 :=
    Nominal.gen p0142 s
  have p0144 :=
    Nominal.gen p0143 d
  have p0145 :=
    @g_dffun2 d s t (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
  have p0146_e01_recanon : Nominal.NPrf (syn_wb (syn_wfun (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))) (.all d (.all s (.all t (.imp (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classEq (.cv s) (.cv t))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0145
  have p0146 :=
    @g_mpbir (syn_wfun (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))) (.all d (.all s (.all t (.imp (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))) (.classEq (.cv s) (.cv t)))))) p0144 p0146_e01_recanon
  exact p0146

#print axioms g_wppqkrelrescnvfunndv

end NFChoice.DirectNominalPrf.WPPReplay
