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
import NominalWPPReplayChunk014Compact001Part016

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

noncomputable def g_unirange2ssfdifx
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_unirange2ssfdifx_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_unirange2ssfdifx_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_unirange2ssfdifx_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wss (syn_cuni (syn_cfdpivrange2 R A B)) (syn_cfdif R A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d_ne_q : d ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_d : q ≠ d :=
    Ne.symm fresh_d_ne_q
  have fresh_d_ne_p : d ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_d : p ≠ d :=
    Ne.symm fresh_d_ne_p
  have fresh_d_ne_x : d ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_d_ne_y : d ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_d : y ≠ d :=
    Ne.symm fresh_d_ne_y
  have fresh_d_ne_c : d ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_d : c ≠ d :=
    Ne.symm fresh_d_ne_c
  have fresh_q_ne_p : q ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have fresh_q_ne_x : q ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_y : q ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_q : y ≠ q :=
    Ne.symm fresh_q_ne_y
  have fresh_q_ne_c : q ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_q : c ≠ q :=
    Ne.symm fresh_q_ne_c
  have fresh_p_ne_x : p ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_ne_y : p ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_y_ne_p : y ≠ p :=
    Ne.symm fresh_p_ne_y
  have fresh_p_ne_c : p ≠ c := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_c_ne_p : c ≠ p :=
    Ne.symm fresh_p_ne_c
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_c : x ≠ c := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_c_ne_x : c ≠ x :=
    Ne.symm fresh_x_ne_c
  have fresh_y_ne_c : y ≠ c := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y :=
    Ne.symm fresh_y_ne_c
  have dv_cache_0001 : q ∉ ((Class.cv d)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cfdpivrange2 R A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : Disjoint (A).fv (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0004 : Disjoint (A).fv ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (A).fv ((Class.cv q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({q} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show q ∉ (A).fv from (by exact fresh_q_not_A))))))
  have dv_cache_0005 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0006 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint (B).fv ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (B).fv ((Class.cv q)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({q} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show q ∉ (B).fv from (by exact fresh_q_not_B))))))
  have dv_cache_0008 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0009 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : Disjoint ((Class.cv q)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint ((Class.cv q)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({q} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show q ∉ (R).fv from (by exact fresh_q_not_R))))))
  have dv_cache_0011 : p ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0018 : Disjoint (A).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show Disjoint (A).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0019 : Disjoint (A).fv ((syn_copk (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show Disjoint (A).fv ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((A).fv) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact fresh_x_not_A)))))), (show Disjoint ((A).fv) (((Class.cv y)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (A).fv from (by exact fresh_y_not_A))))))⟩))))
  have dv_cache_0020 : Disjoint (B).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show Disjoint (B).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0021 : Disjoint (B).fv ((syn_copk (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show Disjoint (B).fv ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((B).fv) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((B).fv) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (B).fv from (by exact fresh_x_not_B)))))), (show Disjoint ((B).fv) (((Class.cv y)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (B).fv from (by exact fresh_y_not_B))))))⟩))))
  have dv_cache_0022 : Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint (({p} : Finset Var)) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({p} : Finset Var)) (((Class.cv x)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) (({x} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show p ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ x from (by exact fresh_p_ne_x)))))))), (show Disjoint (({p} : Finset Var)) (((Class.cv y)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) (({y} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show p ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ y from (by exact fresh_p_ne_y))))))))⟩))))
  have dv_cache_0023 : Disjoint ((Class.cv p)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show Disjoint ((Class.cv p)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0024 : Disjoint ((syn_copk (.cv x) (.cv y))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show Disjoint ((syn_copk (.cv x) (.cv y))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show Disjoint ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) ((R).fv) from (Finset.disjoint_union_left.mpr ⟨(show Disjoint (((Class.cv x)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R)))))), (show Disjoint (((Class.cv y)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show y ∉ (R).fv from (by exact fresh_y_not_R))))))⟩))))
  have dv_cache_0025 : Disjoint (A).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show Disjoint (A).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0026 : Disjoint (A).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (show Disjoint (A).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (A).fv from (by exact fresh_y_not_A))))))
  have dv_cache_0027 : Disjoint (B).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show Disjoint (B).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (B).fv from (by exact fresh_x_not_B))))))
  have dv_cache_0028 : Disjoint (B).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show Disjoint (B).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (B).fv from (by exact fresh_y_not_B))))))
  have dv_cache_0029 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show Disjoint ((Class.cv x)).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x), NFChoice.Compiler.CoreFVSimp.fv_class_cv (y)]; exact (show Disjoint (({x} : Finset Var)) (({y} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y))))))))
  have dv_cache_0030 : Disjoint ((Class.cv x)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0031 : Disjoint ((Class.cv y)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show Disjoint ((Class.cv y)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0032 : y ∉ ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_A, fresh_y_ne_d, fresh_y_ne_q, fresh_y_ne_p, fresh_y_not_B, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : x ∉ ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A, fresh_x_ne_d, fresh_x_ne_q, fresh_x_ne_p, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : c ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : c ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : d ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : c ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : d ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : c ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0041 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0042 : c ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0043 : x ∉ ((Wff.classMem (.cv d) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_d, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0044 : y ∉ ((Wff.classMem (.cv d) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_d, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0045 : y ∉ ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_A, fresh_y_ne_d, fresh_y_ne_q, fresh_y_ne_p, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0046 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0047 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0048 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0049 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0050 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0051 : d ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0052 : d ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (show d ≠ y from (by exact fresh_d_ne_y))
  have dv_cache_0053 : p ∉ ((Wff.classMem (.cv d) (syn_cfdif R A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_d, fresh_p_not_A, fresh_p_not_B, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0054 : p ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, fresh_p_not_A, fresh_p_ne_d, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0055 : q ∉ ((Wff.classMem (.cv d) (syn_cfdif R A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_d, fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0056 : q ∉ ((syn_wbr R (syn_cwe) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0057 : d ∉ ((syn_cuni (syn_cfdpivrange2 R A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0058 : d ∉ ((syn_cfdif R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0059 : d ∉ ((syn_wbr R (syn_cwe) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eluni2 q (.cv d) (syn_cfdpivrange2 R A B) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B))) (syn_wrex q (syn_cfdpivrange2 R A B) (.classMem (.cv d) (.cv q))) p0000
  have p0002 :=
    @g_a1i (.imp (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B))) (syn_wrex q (syn_cfdpivrange2 R A B) (.classMem (.cv d) (.cv q)))) (syn_wbr R (syn_cwe) A) p0001
  have p0003 :=
    @g_fdpivrange2br A B (.cv q) R p dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_unirange2ssfdifx_1 hyp_unirange2ssfdifx_2 hyp_unirange2ssfdifx_3
  have p0004 :=
    @g_biimpi (.classMem (.cv q) (syn_cfdpivrange2 R A B)) (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) p0003
  have p0005 :=
    @g_a1i (.imp (.classMem (.cv q) (syn_cfdpivrange2 R A B)) (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) p0004
  have p0006 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
  have p0007 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))
  have p0008 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classMem (.cv p) (syn_cxpk B B)) p0006 p0007
  have p0009 :=
    @g_elxpk2 x y (.cv p) B B dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0010 :=
    @g_biimpi (.classMem (.cv p) (syn_cxpk B B)) (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))) p0009
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv p) (syn_cxpk B B)) (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))) p0008 p0010
  have p0012 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0013 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0014 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)
  have p0015 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) p0013 p0014
  have p0016 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
  have p0017 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) p0016 p0017
  have p0019 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv d) (.cv q)) p0018 p0019
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv d) (.cv q)) p0015 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classMem (.cv d) (.cv q)) p0012 p0021
  have p0023 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0024 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0025 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) p0024 p0025
  have p0027 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)) p0026 p0027
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)) p0023 p0028
  have p0030 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_cfdminvalp R A B (.cv p)) (.cv q) p0029
  have p0031 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0032 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv x) (.cv y)) R dv_cache_0003 dv_cache_0018 dv_cache_0019 dv_cache_0005 dv_cache_0020 dv_cache_0021 dv_cache_0008 dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))) (.classEq (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))) p0031 p0032
  have p0034 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (.cv q) (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) p0030 p0033
  have p0035 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0036 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0037 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) p0036 p0037
  have p0039 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
  have p0040 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) p0039 p0040
  have p0042 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (syn_wbr R (syn_cwe) A) p0041 p0042
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wbr R (syn_cwe) A) p0038 p0043
  have p0045 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0046 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv x) B) p0045 p0046
  have p0048 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0049 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classMem (.cv x) B) (.classMem (.cv y) B) p0047 p0048
  have p0050 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0044 p0049
  have p0051 :=
    @g_fdminvalpfpivred A B (.cv x) (.cv y) R dv_cache_0003 dv_cache_0025 dv_cache_0026 dv_cache_0005 dv_cache_0027 dv_cache_0028 dv_cache_0008 dv_cache_0029 dv_cache_0030 dv_cache_0031
  have p0052 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) (syn_cfpiv R A (.cv x) (.cv y))) p0050 p0051
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) (syn_cfpiv R A (.cv x) (.cv y))) p0035 p0052
  have p0054 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (.cv q) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) (syn_cfpiv R A (.cv x) (.cv y)) p0034 p0053
  have p0055 :=
    @g_eleqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (.cv d) (.cv q) (syn_cfpiv R A (.cv x) (.cv y)) p0022 p0054
  have p0056 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) p0055
  have p0057 :=
    @g_reximdva (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) y B dv_cache_0032 p0056
  have p0058 :=
    @g_reximdva (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) x B dv_cache_0033 p0057
  have p0059 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0025 dv_cache_0026 dv_cache_0005 dv_cache_0034 dv_cache_0035 dv_cache_0029 dv_cache_0030 dv_cache_0036 dv_cache_0037 dv_cache_0031 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
  have p0060 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) p0059
  have p0061 :=
    @g_simpll (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))
  have p0062 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (.classMem (.cv d) A) p0060 p0061
  have p0063 :=
    @g_a1i (.imp (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) p0062
  have p0064 :=
    @g_rexlimdvva (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A) x y B B dv_cache_0016 dv_cache_0043 dv_cache_0044 dv_cache_0033 dv_cache_0045 dv_cache_0017 p0063
  have p0065 :=
    @g_syld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))) (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))) (.classMem (.cv d) A) p0058 p0064
  have p0066 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0067 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0068 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)
  have p0069 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) p0067 p0068
  have p0070 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
  have p0071 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))
  have p0072 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) p0070 p0071
  have p0073 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv d) (.cv q)) p0072 p0073
  have p0075 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv d) (.cv q)) p0069 p0074
  have p0076 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classMem (.cv d) (.cv q)) p0066 p0075
  have p0077 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0078 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0079 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) p0078 p0079
  have p0081 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
  have p0082 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)) p0080 p0081
  have p0083 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)) p0077 p0082
  have p0084 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_cfdminvalp R A B (.cv p)) (.cv q) p0083
  have p0085 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0086 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv x) (.cv y)) R dv_cache_0003 dv_cache_0018 dv_cache_0019 dv_cache_0005 dv_cache_0020 dv_cache_0021 dv_cache_0008 dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0087 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))) (.classEq (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))) p0085 p0086
  have p0088 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (.cv q) (syn_cfdminvalp R A B (.cv p)) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) p0084 p0087
  have p0089 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0090 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0091 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)
  have p0092 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) p0090 p0091
  have p0093 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
  have p0094 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))
  have p0095 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) p0093 p0094
  have p0096 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (syn_wbr R (syn_cwe) A) p0095 p0096
  have p0098 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wbr R (syn_cwe) A) p0092 p0097
  have p0099 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0100 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)
  have p0101 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv x) B) p0099 p0100
  have p0102 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)
  have p0103 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classMem (.cv x) B) (.classMem (.cv y) B) p0101 p0102
  have p0104 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0098 p0103
  have p0105 :=
    @g_fdminvalpfpivred A B (.cv x) (.cv y) R dv_cache_0003 dv_cache_0025 dv_cache_0026 dv_cache_0005 dv_cache_0027 dv_cache_0028 dv_cache_0008 dv_cache_0029 dv_cache_0030 dv_cache_0031
  have p0106 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) (syn_cfpiv R A (.cv x) (.cv y))) p0104 p0105
  have p0107 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) (syn_cfpiv R A (.cv x) (.cv y))) p0089 p0106
  have p0108 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (.cv q) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) (syn_cfpiv R A (.cv x) (.cv y)) p0088 p0107
  have p0109 :=
    @g_eleqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (.cv d) (.cv q) (syn_cfpiv R A (.cv x) (.cv y)) p0076 p0108
  have p0110 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) p0109
  have p0111 :=
    @g_reximdva (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) y B dv_cache_0032 p0110
  have p0112 :=
    @g_reximdva (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))) (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) x B dv_cache_0033 p0111
  have p0113 :=
    @g_jcad (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))) (.classMem (.cv d) A) (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))) p0065 p0112
  have p0114 :=
    @g_elfdif x y A B R d dv_cache_0003 dv_cache_0005 dv_cache_0035 dv_cache_0046 dv_cache_0047 dv_cache_0008 dv_cache_0048 dv_cache_0015 dv_cache_0016 dv_cache_0041 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0017
  have p0115 :=
    @g_biimpri (.classMem (.cv d) (syn_cfdif R A B)) (syn_wa (.classMem (.cv d) A) (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))) p0114
  have p0116 :=
    @g_syl6 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))) (syn_wa (.classMem (.cv d) A) (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))) (.classMem (.cv d) (syn_cfdif R A B)) p0113 p0115
  have p0117 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))) (.classMem (.cv d) (syn_cfdif R A B)) p0011 p0116
  have p0118 :=
    @g_ex (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)) (.classMem (.cv d) (syn_cfdif R A B)) p0117
  have p0119 :=
    @g_rexlimdva (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)) (.classMem (.cv d) (syn_cfdif R A B)) p (syn_cxpk B B) dv_cache_0053 dv_cache_0054 p0118
  have p0120 :=
    @g_syld (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (.classMem (.cv q) (syn_cfdpivrange2 R A B)) (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv d) (syn_cfdif R A B)) p0005 p0119
  have p0121 :=
    @g_ex (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)) (.imp (.classMem (.cv q) (syn_cfdpivrange2 R A B)) (.classMem (.cv d) (syn_cfdif R A B))) p0120
  have p0122 :=
    @g_com23 (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)) (.classMem (.cv q) (syn_cfdpivrange2 R A B)) (.classMem (.cv d) (syn_cfdif R A B)) p0121
  have p0123 :=
    @g_rexlimdv (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)) (.classMem (.cv d) (syn_cfdif R A B)) q (syn_cfdpivrange2 R A B) dv_cache_0055 dv_cache_0056 p0122
  have p0124 :=
    @g_syld (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B))) (syn_wrex q (syn_cfdpivrange2 R A B) (.classMem (.cv d) (.cv q))) (.classMem (.cv d) (syn_cfdif R A B)) p0002 p0123
  have p0125 :=
    @g_ssrdv (syn_wbr R (syn_cwe) A) d (syn_cuni (syn_cfdpivrange2 R A B)) (syn_cfdif R A B) dv_cache_0057 dv_cache_0058 dv_cache_0059 p0124
  exact p0125

#print axioms g_unirange2ssfdifx

end NFChoice.DirectNominalPrf.WPPReplay
