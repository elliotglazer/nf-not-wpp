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
import NominalWPPReplayChunk013Compact001Part049

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

noncomputable def g_sbth
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.imp (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) A)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let g : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let d : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (h))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_g_ne_b : g ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_g : b ≠ g :=
    Ne.symm fresh_g_ne_b
  have fresh_g_ne_d : g ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_d_ne_g : d ≠ g :=
    Ne.symm fresh_g_ne_d
  have fresh_g_ne_a : g ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_g : a ≠ g :=
    Ne.symm fresh_g_ne_a
  have fresh_b_ne_d : b ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_d_ne_b : d ≠ b :=
    Ne.symm fresh_b_ne_d
  have fresh_b_ne_a : b ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_b : a ≠ b :=
    Ne.symm fresh_b_ne_a
  have fresh_d_ne_a : d ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_d : a ≠ d :=
    Ne.symm fresh_d_ne_a
  have dv_cache_0001 : g ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : g ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show g ≠ b from (by exact fresh_g_ne_b))
  have dv_cache_0005 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : d ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show d ≠ a from (by exact fresh_d_ne_a))
  have dv_cache_0009 : a ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_wss (.cv g) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_g, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((syn_wss (.cv d) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_d, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0014 : d ∉ ((syn_wrex b B (syn_wss (.cv g) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_B, fresh_d_ne_g, fresh_d_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : g ∉ ((syn_wrex a A (syn_wss (.cv d) (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_ne_d, fresh_g_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : g ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show g ≠ d from (by exact fresh_g_ne_d))
  have dv_cache_0017 : a ∉ ((syn_cnc (.cv d))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((Wff.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_g, fresh_b_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((Wff.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_g, fresh_a_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : b ∉ ((syn_cnc (.cv d))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((syn_cnc (.cv g))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : b ∉ ((Wff.classEq A (syn_cnc (.cv g)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : g ∉ ((Wff.classEq A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : d ∉ ((Wff.classEq A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : g ∉ ((syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : d ∉ ((syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brlecg g b A B (syn_cncs) (syn_cncs) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_brlecg d a B A (syn_cncs) (syn_cncs) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0002 :=
    @g_ancoms (.classMem B (syn_cncs)) (.classMem A (syn_cncs)) (syn_wb (syn_wbr B (syn_clec) A) (syn_wrex d B (syn_wrex a A (syn_wss (.cv d) (.cv a))))) p0001
  have p0003 :=
    @g_anbi12d (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wbr A (syn_clec) B) (syn_wrex g A (syn_wrex b B (syn_wss (.cv g) (.cv b)))) (syn_wbr B (syn_clec) A) (syn_wrex d B (syn_wrex a A (syn_wss (.cv d) (.cv a)))) p0000 p0002
  have p0004 :=
    @g_reeanv (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)) b a B A dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0005 :=
    @g_n_2rexbii (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) (syn_wa (syn_wrex b B (syn_wss (.cv g) (.cv b))) (syn_wrex a A (syn_wss (.cv d) (.cv a)))) g d A B p0004
  have p0006 :=
    @g_reeanv (syn_wrex b B (syn_wss (.cv g) (.cv b))) (syn_wrex a A (syn_wss (.cv d) (.cv a))) g d A B dv_cache_0006 dv_cache_0002 dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0007 :=
    @g_bitri (syn_wrex g A (syn_wrex d B (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))))) (syn_wrex g A (syn_wrex d B (syn_wa (syn_wrex b B (syn_wss (.cv g) (.cv b))) (syn_wrex a A (syn_wss (.cv d) (.cv a)))))) (syn_wa (syn_wrex g A (syn_wrex b B (syn_wss (.cv g) (.cv b)))) (syn_wrex d B (syn_wrex a A (syn_wss (.cv d) (.cv a))))) p0005 p0006
  have p0008 :=
    @g_syl6bbr (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) A)) (syn_wa (syn_wrex g A (syn_wrex b B (syn_wss (.cv g) (.cv b)))) (syn_wrex d B (syn_wrex a A (syn_wss (.cv d) (.cv a))))) (syn_wrex g A (syn_wrex d B (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))))) p0003 p0007
  have p0009 :=
    @g_ncseqnc A (.cv g)
  have p0010 :=
    @g_ncseqnc B (.cv d)
  have p0011 :=
    @g_bi2anan9 (.classMem A (syn_cncs)) (.classEq A (syn_cnc (.cv g))) (.classMem (.cv g) A) (.classMem B (syn_cncs)) (.classEq B (syn_cnc (.cv d))) (.classMem (.cv d) B) p0009 p0010
  have p0012 :=
    @g_biimpar (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (.classEq A (syn_cnc (.cv g))) (.classEq B (syn_cnc (.cv d)))) (syn_wa (.classMem (.cv g) A) (.classMem (.cv d) B)) p0011
  have p0013 :=
    @g_simplr (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))
  have p0014 :=
    @g_ensym (.cv a) (.cv g)
  have p0015 :=
    @g_sylib (syn_wa (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))) (syn_wbr (.cv a) (syn_cen) (.cv g)) (syn_wbr (.cv g) (syn_cen) (.cv a)) p0013 p0014
  have p0016 :=
    @g_simprl (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))) (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))
  have p0017 :=
    @g_simpll (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g)) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))
  have p0018 :=
    @g_simprr (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))) (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))
  have p0019 :=
    @g_sbthlem3 (.cv a) (.cv b) (.cv g) (.cv d)
  have p0020 :=
    @g_syl22anc (syn_wa (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))) (syn_wbr (.cv a) (syn_cen) (.cv g)) (syn_wss (.cv g) (.cv b)) (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wss (.cv d) (.cv a)) (syn_wbr (.cv a) (syn_cen) (.cv b)) p0013 p0016 p0017 p0018 p0019
  have p0021 :=
    @g_entr (.cv g) (.cv a) (.cv b)
  have p0022 :=
    @g_syl2anc (syn_wa (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))) (syn_wbr (.cv g) (syn_cen) (.cv a)) (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wbr (.cv g) (syn_cen) (.cv b)) p0015 p0020 p0021
  have p0023 :=
    @g_entr (.cv g) (.cv b) (.cv d)
  have p0024 :=
    @g_syl2anc (syn_wa (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))) (syn_wbr (.cv g) (syn_cen) (.cv b)) (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv g) (syn_cen) (.cv d)) p0022 p0017 p0023
  have p0025 :=
    @g_ex (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))) (syn_wbr (.cv g) (syn_cen) (.cv d)) p0024
  have p0026 :=
    @g_elnc (.cv b) (.cv d)
  have p0027 :=
    @g_elnc (.cv a) (.cv g)
  have p0028 :=
    @g_anbi12i (.classMem (.cv b) (syn_cnc (.cv d))) (syn_wbr (.cv b) (syn_cen) (.cv d)) (.classMem (.cv a) (syn_cnc (.cv g))) (syn_wbr (.cv a) (syn_cen) (.cv g)) p0026 p0027
  have p0029 :=
    @g_vex g
  have p0030 :=
    @g_eqnc (.cv g) (.cv d) p0029
  have p0031 :=
    @g_imbi2i (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d))) (syn_wbr (.cv g) (syn_cen) (.cv d)) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))) p0030
  have p0032 :=
    @g_n_3imtr4i (syn_wa (syn_wbr (.cv b) (syn_cen) (.cv d)) (syn_wbr (.cv a) (syn_cen) (.cv g))) (.imp (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))) (syn_wbr (.cv g) (syn_cen) (.cv d))) (syn_wa (.classMem (.cv b) (syn_cnc (.cv d))) (.classMem (.cv a) (syn_cnc (.cv g)))) (.imp (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))) (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d)))) p0025 p0028 p0031
  have p0033 :=
    @g_rexlimivv (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))) (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d))) b a (syn_cnc (.cv d)) (syn_cnc (.cv g)) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0013 p0032
  have p0034 :=
    @g_rexeq (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))) b B (syn_cnc (.cv d)) dv_cache_0003 dv_cache_0020
  have p0035 :=
    @g_rexeq (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))) a A (syn_cnc (.cv g)) dv_cache_0007 dv_cache_0021
  have p0036 :=
    @g_rexbidv (.classEq A (syn_cnc (.cv g))) (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))) (syn_wrex a (syn_cnc (.cv g)) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a)))) b (syn_cnc (.cv d)) dv_cache_0022 p0035
  have p0037 :=
    @g_sylan9bbr (.classEq B (syn_cnc (.cv d))) (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) (syn_wrex b (syn_cnc (.cv d)) (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) (.classEq A (syn_cnc (.cv g))) (syn_wrex b (syn_cnc (.cv d)) (syn_wrex a (syn_cnc (.cv g)) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) p0034 p0036
  have p0038 :=
    @g_eqeq12 A (syn_cnc (.cv g)) B (syn_cnc (.cv d))
  have p0039 :=
    @g_imbi12d (syn_wa (.classEq A (syn_cnc (.cv g))) (.classEq B (syn_cnc (.cv d)))) (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) (syn_wrex b (syn_cnc (.cv d)) (syn_wrex a (syn_cnc (.cv g)) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) (.classEq A B) (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d))) p0037 p0038
  have p0040 :=
    @g_mpbiri (syn_wa (.classEq A (syn_cnc (.cv g))) (.classEq B (syn_cnc (.cv d)))) (.imp (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) (.classEq A B)) (.imp (syn_wrex b (syn_cnc (.cv d)) (syn_wrex a (syn_cnc (.cv g)) (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) (.classEq (syn_cnc (.cv g)) (syn_cnc (.cv d)))) p0033 p0039
  have p0041 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (.classMem (.cv g) A) (.classMem (.cv d) B))) (syn_wa (.classEq A (syn_cnc (.cv g))) (.classEq B (syn_cnc (.cv d)))) (.imp (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) (.classEq A B)) p0012 p0040
  have p0042 :=
    @g_rexlimdvva (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))) (.classEq A B) g d A B dv_cache_0006 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0016 p0041
  have p0043 :=
    @g_sylbid (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) A)) (syn_wrex g A (syn_wrex d B (syn_wrex b B (syn_wrex a A (syn_wa (syn_wss (.cv g) (.cv b)) (syn_wss (.cv d) (.cv a))))))) (.classEq A B) p0008 p0042
  exact p0043

noncomputable def g_ltlenlec
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wb (syn_wbr M (syn_cltc) N) (syn_wa (syn_wbr M (syn_clec) N) (.neg (syn_wbr N (syn_clec) M))))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  have p0000 :=
    @g_brltc M N
  have p0001 :=
    @g_nclecid M
  have p0002 :=
    @g_breq1 M N M (syn_clec)
  have p0003 :=
    @g_syl5ibcom (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) M) (.classEq M N) (syn_wbr N (syn_clec) M) p0001 p0002
  have p0004 :=
    @g_ad2antrr (.classMem M (syn_cncs)) (.imp (.classEq M N) (syn_wbr N (syn_clec) M)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) N) p0003
  have p0005 :=
    @g_sbth M N
  have p0006 :=
    @g_expdimp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) N) (syn_wbr N (syn_clec) M) (.classEq M N) p0005
  have p0007 :=
    @g_impbid (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) N)) (.classEq M N) (syn_wbr N (syn_clec) M) p0004 p0006
  have p0008 :=
    @g_necon3abid (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) N)) (syn_wbr N (syn_clec) M) M N p0007
  have p0009 :=
    @g_pm5_32da (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) N) (syn_wne M N) (.neg (syn_wbr N (syn_clec) M)) p0008
  have p0010 :=
    @g_syl5bb (syn_wbr M (syn_cltc) N) (syn_wa (syn_wbr M (syn_clec) N) (syn_wne M N)) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wa (syn_wbr M (syn_clec) N) (.neg (syn_wbr N (syn_clec) M))) p0000 p0009
  exact p0010

noncomputable def g_addlec
    (M : Class) (N : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M V) (.classMem N W) (syn_wne (syn_cplc M N) (syn_c0))) (syn_wbr M (syn_clec) (syn_cplc M N))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_M : z ∉ M.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_N : z ∉ N.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : y ∉ ((syn_wss (.cv x) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cplc M N)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_M, fresh_z_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cplc M N)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, fresh_x_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have p0000 :=
    @g_eladdc (.cv z) M N x y dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_ssun1 (.cv x) (.cv y)
  have p0002 :=
    @g_sseq2 (.cv z) (syn_cun (.cv x) (.cv y)) (.cv x)
  have p0003 :=
    @g_mpbiri (.classEq (.cv z) (syn_cun (.cv x) (.cv y))) (syn_wss (.cv x) (.cv z)) (syn_wss (.cv x) (syn_cun (.cv x) (.cv y))) p0001 p0002
  have p0004 :=
    @g_adantl (.classEq (.cv z) (syn_cun (.cv x) (.cv y))) (syn_wss (.cv x) (.cv z)) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) p0003
  have p0005 :=
    @g_rexlimivw (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv x) (.cv y)))) (syn_wss (.cv x) (.cv z)) y N dv_cache_0008 p0004
  have p0006 :=
    @g_reximi (syn_wrex y N (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv x) (.cv y))))) (syn_wss (.cv x) (.cv z)) x M p0005
  have p0007 :=
    @g_sylbi (.classMem (.cv z) (syn_cplc M N)) (syn_wrex x M (syn_wrex y N (syn_wa (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv x) (.cv y)))))) (syn_wrex x M (syn_wss (.cv x) (.cv z))) p0000 p0006
  have p0008 :=
    @g_ancli (.classMem (.cv z) (syn_cplc M N)) (syn_wrex x M (syn_wss (.cv x) (.cv z))) p0007
  have p0009 :=
    @g_eximi (.classMem (.cv z) (syn_cplc M N)) (syn_wa (.classMem (.cv z) (syn_cplc M N)) (syn_wrex x M (syn_wss (.cv x) (.cv z)))) z p0008
  have p0010 :=
    @g_n0 z (syn_cplc M N) dv_cache_0009
  have p0011 :=
    @g_rexcom (syn_wss (.cv x) (.cv z)) x z M (syn_cplc M N) dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0012 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex z (syn_cplc M N) (syn_wrex x M (syn_wss (.cv x) (.cv z))))))
  have p0013 :=
    @g_bitri (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z)))) (syn_wrex z (syn_cplc M N) (syn_wrex x M (syn_wss (.cv x) (.cv z)))) (syn_wex z (syn_wa (.classMem (.cv z) (syn_cplc M N)) (syn_wrex x M (syn_wss (.cv x) (.cv z))))) p0011 p0012
  have p0014 :=
    @g_n_3imtr4i (syn_wex z (.classMem (.cv z) (syn_cplc M N))) (syn_wex z (syn_wa (.classMem (.cv z) (syn_cplc M N)) (syn_wrex x M (syn_wss (.cv x) (.cv z))))) (syn_wne (syn_cplc M N) (syn_c0)) (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z)))) p0009 p0010 p0013
  have p0015 :=
    @g_n_3ad2ant3 (syn_wne (syn_cplc M N) (syn_c0)) (.classMem M V) (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z)))) (.classMem N W) p0014
  have p0016 :=
    @g_addcexg M N V W
  have p0017 :=
    @g_brlecg x z M (syn_cplc M N) V (syn_cvv) dv_cache_0003 dv_cache_0011 dv_cache_0009 dv_cache_0012
  have p0018 :=
    @g_syldan (.classMem M V) (.classMem N W) (.classMem (syn_cplc M N) (syn_cvv)) (syn_wb (syn_wbr M (syn_clec) (syn_cplc M N)) (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z))))) p0016 p0017
  have p0019 :=
    @g_n_3adant3 (.classMem M V) (.classMem N W) (syn_wb (syn_wbr M (syn_clec) (syn_cplc M N)) (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z))))) (syn_wne (syn_cplc M N) (syn_c0)) p0018
  have p0020 :=
    @g_mpbird (syn_w3a (.classMem M V) (.classMem N W) (syn_wne (syn_cplc M N) (syn_c0))) (syn_wbr M (syn_clec) (syn_cplc M N)) (syn_wrex x M (syn_wrex z (syn_cplc M N) (syn_wss (.cv x) (.cv z)))) p0015 p0019
  exact p0020

noncomputable def g_addlecncs
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) (syn_cplc M N))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  have p0000 :=
    @g_ncaddccl M N
  have p0001 :=
    @g_nulnnc
  have p0002 :=
    @g_eleq1 (syn_cplc M N) (syn_c0) (syn_cncs)
  have p0003 :=
    @g_mtbiri (.classEq (syn_cplc M N) (syn_c0)) (.classMem (syn_cplc M N) (syn_cncs)) (.classMem (syn_c0) (syn_cncs)) p0001 p0002
  have p0004 :=
    @g_necon2ai (.classMem (syn_cplc M N) (syn_cncs)) (syn_cplc M N) (syn_c0) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (syn_cplc M N) (syn_cncs)) (syn_wne (syn_cplc M N) (syn_c0)) p0000 p0004
  have p0006 :=
    @g_addlec M N (syn_cncs) (syn_cncs)
  have p0007 :=
    @g_mpd3an3 (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wne (syn_cplc M N) (syn_c0)) (syn_wbr M (syn_clec) (syn_cplc M N)) p0005 p0006
  exact p0007

noncomputable def g_dflec2
    (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv) (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wb (syn_wbr M (syn_clec) N) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({p} : Finset Var)
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_p : a ≠ p := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_p : b ≠ p := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_b : p ≠ b :=
    Ne.symm fresh_b_ne_p
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : a ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0005 : p ∉ ((syn_cnc (syn_cdif (.cv b) (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_b, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((Wff.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_b, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_wa (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_p, fresh_p_ne_b, dv_M_p, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : b ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, fresh_a_not_M, fresh_a_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_N, fresh_b_not_M, fresh_b_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_M, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_M, fresh_b_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((syn_wbr M (syn_clec) N)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_p, dv_N_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : p ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_p, dv_N_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brlecg a b M N (syn_cncs) (syn_cncs) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_ncseqnc M (.cv a)
  have p0002 :=
    @g_ncseqnc N (.cv b)
  have p0003 :=
    @g_bi2anan9 (.classMem M (syn_cncs)) (.classEq M (syn_cnc (.cv a))) (.classMem (.cv a) M) (.classMem N (syn_cncs)) (.classEq N (syn_cnc (.cv b))) (.classMem (.cv b) N) p0001 p0002
  have p0004 :=
    @g_biimpar (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wa (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))) (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N)) p0003
  have p0005 :=
    @g_vex b
  have p0006 :=
    @g_vex a
  have p0007 :=
    @g_difex (.cv b) (.cv a) p0005 p0006
  have p0008 :=
    @g_ncelncsi (syn_cdif (.cv b) (.cv a)) p0007
  have p0009 :=
    @g_disjdif (.cv a) (.cv b)
  have p0010 :=
    @g_ncdisjun (.cv a) (syn_cdif (.cv b) (.cv a)) p0006 p0007
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_undif2 (.cv a) (.cv b)
  have p0013 :=
    @g_ssequn1 (.cv a) (.cv b)
  have p0014 :=
    @g_biimpi (syn_wss (.cv a) (.cv b)) (.classEq (syn_cun (.cv a) (.cv b)) (.cv b)) p0013
  have p0015 :=
    @g_syl5eq (syn_wss (.cv a) (.cv b)) (syn_cun (.cv a) (syn_cdif (.cv b) (.cv a))) (syn_cun (.cv a) (.cv b)) (.cv b) p0012 p0014
  have p0016 :=
    @g_nceqd (syn_wss (.cv a) (.cv b)) (syn_cun (.cv a) (syn_cdif (.cv b) (.cv a))) (.cv b) p0015
  have p0017 :=
    @g_syl5reqr (syn_wss (.cv a) (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a)))) (syn_cnc (syn_cun (.cv a) (syn_cdif (.cv b) (.cv a)))) (syn_cnc (.cv b)) p0011 p0016
  have p0018 :=
    @g_addceq2 (.cv p) (syn_cnc (syn_cdif (.cv b) (.cv a))) (syn_cnc (.cv a))
  have p0019 :=
    @g_eqeq2d (.classEq (.cv p) (syn_cnc (syn_cdif (.cv b) (.cv a)))) (syn_cplc (syn_cnc (.cv a)) (.cv p)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a)))) (syn_cnc (.cv b)) p0018
  have p0020 :=
    @g_rspcev (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p))) (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a))))) p (syn_cnc (syn_cdif (.cv b) (.cv a))) (syn_cncs) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0019
  have p0021 :=
    @g_sylancr (syn_wss (.cv a) (.cv b)) (.classMem (syn_cnc (syn_cdif (.cv b) (.cv a))) (syn_cncs)) (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (syn_cnc (syn_cdif (.cv b) (.cv a))))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p)))) p0008 p0017 p0020
  have p0022 :=
    @g_id (.classEq N (syn_cnc (.cv b)))
  have p0023 :=
    @g_addceq1 M (syn_cnc (.cv a)) (.cv p)
  have p0024 :=
    @g_eqeqan12d (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a))) N (syn_cnc (.cv b)) (syn_cplc M (.cv p)) (syn_cplc (syn_cnc (.cv a)) (.cv p)) p0022 p0023
  have p0025 :=
    @g_rexbidv (syn_wa (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a)))) (.classEq N (syn_cplc M (.cv p))) (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p))) p (syn_cncs) dv_cache_0008 p0024
  have p0026 :=
    @g_ancoms (.classEq N (syn_cnc (.cv b))) (.classEq M (syn_cnc (.cv a))) (syn_wb (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p))))) p0025
  have p0027 :=
    @g_syl5ibr (syn_wss (.cv a) (.cv b)) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))) (syn_wa (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))) (syn_wrex p (syn_cncs) (.classEq (syn_cnc (.cv b)) (syn_cplc (syn_cnc (.cv a)) (.cv p)))) p0021 p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))) (syn_wa (.classEq M (syn_cnc (.cv a))) (.classEq N (syn_cnc (.cv b)))) (.imp (syn_wss (.cv a) (.cv b)) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p))))) p0004 p0027
  have p0029 :=
    @g_rexlimdvva (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wss (.cv a) (.cv b)) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))) a b M N dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0004 p0028
  have p0030 :=
    @g_sylbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) N) (syn_wrex a M (syn_wrex b N (syn_wss (.cv a) (.cv b)))) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))) p0000 p0029
  have p0031 :=
    @g_addlecncs M (.cv p)
  have p0032 :=
    @g_breq2 N (syn_cplc M (.cv p)) M (syn_clec)
  have p0033 :=
    @g_syl5ibrcom (syn_wa (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs))) (syn_wbr M (syn_clec) N) (.classEq N (syn_cplc M (.cv p))) (syn_wbr M (syn_clec) (syn_cplc M (.cv p))) p0031 p0032
  have p0034 :=
    @g_adantlr (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs)) (.imp (.classEq N (syn_cplc M (.cv p))) (syn_wbr M (syn_clec) N)) (.classMem N (syn_cncs)) p0033
  have p0035 :=
    @g_rexlimdva (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classEq N (syn_cplc M (.cv p))) (syn_wbr M (syn_clec) N) p (syn_cncs) dv_cache_0014 dv_cache_0015 p0034
  have p0036 :=
    @g_impbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) N) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))) p0030 p0035
  exact p0036

#print axioms g_dflec2

end NFChoice.DirectNominalPrf.WPPReplay
