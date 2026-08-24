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
import NominalWPPReplayChunk012BCompact001Part010

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

noncomputable def g_funsi
    (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wfun (syn_csi F))) := by
  let proofSupport : Finset Var := F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (h)
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (h)
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (h)
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (h)
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
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_x_ne_c : x ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_x : c ≠ x :=
    Ne.symm fresh_x_ne_c
  have fresh_x_ne_d : x ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_x : d ≠ x :=
    Ne.symm fresh_x_ne_d
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_y_ne_c : y ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y :=
    Ne.symm fresh_y_ne_c
  have fresh_y_ne_d : y ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_y : d ≠ y :=
    Ne.symm fresh_y_ne_d
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_z_ne_c : z ≠ c := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_c_ne_z : c ≠ z :=
    Ne.symm fresh_z_ne_c
  have fresh_z_ne_d : z ≠ d := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_d_ne_z : d ≠ z :=
    Ne.symm fresh_z_ne_d
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_a_ne_d : a ≠ d := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_d_ne_a : d ≠ a :=
    Ne.symm fresh_a_ne_d
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have fresh_b_ne_d : b ≠ d := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_d_ne_b : d ≠ b :=
    Ne.symm fresh_b_ne_d
  have fresh_c_ne_d : c ≠ d := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_d_ne_c : d ≠ c :=
    Ne.symm fresh_c_ne_d
  have dv_cache_0001 : a ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0008 : c ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : c ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : c ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : d ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : c ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0015 : d ∉ ((syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_b, fresh_d_not_F, fresh_d_ne_x, fresh_d_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : c ∉ ((syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_b, fresh_c_not_F, fresh_c_ne_x, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_c, fresh_a_ne_d, fresh_a_not_F, fresh_a_ne_x, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_c, fresh_b_ne_d, fresh_b_not_F, fresh_b_ne_x, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : d ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show d ≠ a from (by exact fresh_d_ne_a))
  have dv_cache_0020 : b ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0021 : c ∉ ((Wff.objEq y z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : d ∉ ((Wff.objEq y z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_y, fresh_d_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : c ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : d ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : a ∉ ((Wff.objEq y z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : b ∉ ((Wff.objEq y z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : b ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : z ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : x ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : y ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : x ∉ ((syn_csi F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : y ∉ ((syn_csi F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : z ∉ ((syn_csi F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0036 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0037 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_brsi a b (.cv x) (.cv y) F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_brsi c d (.cv x) (.cv z) F dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0002 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_csi F) (.cv y)) (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))))) (syn_wbr (.cv x) (syn_csi F) (.cv z)) (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))))) p0000 p0001
  have p0003 :=
    @g_ee4anv (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) a b c d dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0004 :=
    @g_bitr4i (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y)) (syn_wbr (.cv x) (syn_csi F) (.cv z))) (syn_wa (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))))) (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))))) (syn_wex a (syn_wex b (syn_wex c (syn_wex d (syn_wa (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))))))) p0002 p0003
  have p0005 :=
    @g_fununiq (.cv a) (.cv b) (.cv d) F
  have p0006_e00_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wfun F) (syn_wbr (.cv a) F (.cv b)) (syn_wbr (.cv a) F (.cv d))) (.objEq b d)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_wbr syn_cop syn_cun syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0005
  have p0006 :=
    @g_n_3exp (syn_wfun F) (syn_wbr (.cv a) F (.cv b)) (syn_wbr (.cv a) F (.cv d)) (.objEq b d) p0006_e00_recanon
  have p0007 :=
    @g_breq1 (.cv a) (.cv c) (.cv d) F
  have p0008_e00_recanon : Nominal.NPrf (.imp (.objEq a c) (syn_wb (syn_wbr (.cv a) F (.cv d)) (syn_wbr (.cv c) F (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0008 :=
    @g_bicomd (.objEq a c) (syn_wbr (.cv a) F (.cv d)) (syn_wbr (.cv c) F (.cv d)) p0008_e00_recanon
  have p0009 :=
    @g_adantr (.objEq a c) (syn_wb (syn_wbr (.cv c) F (.cv d)) (syn_wbr (.cv a) F (.cv d))) (.classEq (.cv z) (syn_csn (.cv d))) p0008
  have p0010 :=
    @g_eqeq2 (.cv z) (syn_csn (.cv d)) (syn_csn (.cv b))
  have p0011 :=
    @g_vex b
  have p0012 :=
    @g_sneqb (.cv b) (.cv d) p0011
  have p0013_e01_recanon : Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv b)) (syn_csn (.cv d))) (.objEq b d)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0012
  have p0013 :=
    @g_syl6bb (.classEq (.cv z) (syn_csn (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z)) (.classEq (syn_csn (.cv b)) (syn_csn (.cv d))) (.objEq b d) p0010 p0013_e01_recanon
  have p0014 :=
    @g_adantl (.classEq (.cv z) (syn_csn (.cv d))) (syn_wb (.classEq (syn_csn (.cv b)) (.cv z)) (.objEq b d)) (.objEq a c) p0013
  have p0015 :=
    @g_imbi12d (syn_wa (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d)))) (syn_wbr (.cv c) F (.cv d)) (syn_wbr (.cv a) F (.cv d)) (.classEq (syn_csn (.cv b)) (.cv z)) (.objEq b d) p0009 p0014
  have p0016 :=
    @g_biimprcd (syn_wa (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d)))) (.imp (syn_wbr (.cv c) F (.cv d)) (.classEq (syn_csn (.cv b)) (.cv z))) (.imp (syn_wbr (.cv a) F (.cv d)) (.objEq b d)) p0015
  have p0017 :=
    @g_exp3a (.imp (syn_wbr (.cv a) F (.cv d)) (.objEq b d)) (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (.imp (syn_wbr (.cv c) F (.cv d)) (.classEq (syn_csn (.cv b)) (.cv z))) p0016
  have p0018 :=
    @g_n_3impd (.imp (syn_wbr (.cv a) F (.cv d)) (.objEq b d)) (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)) (.classEq (syn_csn (.cv b)) (.cv z)) p0017
  have p0019 :=
    @g_syl6 (syn_wfun F) (syn_wbr (.cv a) F (.cv b)) (.imp (syn_wbr (.cv a) F (.cv d)) (.objEq b d)) (.imp (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z))) p0006 p0018
  have p0020 :=
    @g_eqeq1 (.cv x) (syn_csn (.cv a)) (syn_csn (.cv c))
  have p0021 :=
    @g_vex a
  have p0022 :=
    @g_sneqb (.cv a) (.cv c) p0021
  have p0023_e01_recanon : Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv a)) (syn_csn (.cv c))) (.objEq a c)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0022
  have p0023 :=
    @g_syl6bb (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv a)) (syn_csn (.cv c))) (.objEq a c) p0020 p0023_e01_recanon
  have p0024 :=
    @g_n_3anbi1d (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv x) (syn_csn (.cv c))) (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)) p0023
  have p0025 :=
    @g_adantr (.classEq (.cv x) (syn_csn (.cv a))) (syn_wb (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))) (.classEq (.cv y) (syn_csn (.cv b))) p0024
  have p0026 :=
    @g_eqeq1 (.cv y) (syn_csn (.cv b)) (.cv z)
  have p0027_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (syn_csn (.cv b))) (syn_wb (.objEq y z) (.classEq (syn_csn (.cv b)) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0026
  have p0027 :=
    @g_adantl (.classEq (.cv y) (syn_csn (.cv b))) (syn_wb (.objEq y z) (.classEq (syn_csn (.cv b)) (.cv z))) (.classEq (.cv x) (syn_csn (.cv a))) p0027_e00_recanon
  have p0028 :=
    @g_imbi12d (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z) (.classEq (syn_csn (.cv b)) (.cv z)) p0025 p0027
  have p0029 :=
    @g_imbi2d (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))) (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z)) (.imp (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z))) (syn_wbr (.cv a) F (.cv b)) p0028
  have p0030 :=
    @g_biimprcd (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))) (.imp (syn_wbr (.cv a) F (.cv b)) (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z))) (.imp (syn_wbr (.cv a) F (.cv b)) (.imp (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z)))) p0029
  have p0031 :=
    @g_exp3a (.imp (syn_wbr (.cv a) F (.cv b)) (.imp (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z)))) (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.imp (syn_wbr (.cv a) F (.cv b)) (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z))) p0030
  have p0032 :=
    @g_n_3impd (.imp (syn_wbr (.cv a) F (.cv b)) (.imp (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z)))) (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b)) (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z)) p0031
  have p0033 :=
    @g_syl (syn_wfun F) (.imp (syn_wbr (.cv a) F (.cv b)) (.imp (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z)))) (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))) (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z))) p0019 p0032
  have p0034 :=
    @g_imp3a (syn_wfun F) (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z) p0033
  have p0035 :=
    @g_exlimdvv (syn_wfun F) (syn_wa (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))) (.objEq y z) c d dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0034
  have p0036 :=
    @g_exlimdvv (syn_wfun F) (syn_wex c (syn_wex d (syn_wa (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))))) (.objEq y z) a b dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 p0035
  have p0037 :=
    @g_syl5bi (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y)) (syn_wbr (.cv x) (syn_csi F) (.cv z))) (syn_wex a (syn_wex b (syn_wex c (syn_wex d (syn_wa (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))))))) (syn_wfun F) (.objEq y z) p0004 p0036
  have p0038 :=
    @g_alrimiv (syn_wfun F) (.imp (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y)) (syn_wbr (.cv x) (syn_csi F) (.cv z))) (.objEq y z)) z dv_cache_0029 p0037
  have p0039 :=
    @g_alrimivv (syn_wfun F) (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y)) (syn_wbr (.cv x) (syn_csi F) (.cv z))) (.objEq y z))) x y dv_cache_0030 dv_cache_0031 p0038
  have p0040 :=
    @g_dffun2 x y z (syn_csi F) dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
  have p0041 :=
    @g_sylibr (syn_wfun F) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y)) (syn_wbr (.cv x) (syn_csi F) (.cv z))) (.objEq y z))))) (syn_wfun (syn_csi F)) p0039 p0040
  exact p0041

noncomputable def g_rnsi
    (R : Class) :
    Nominal.NPrf (.classEq (syn_crn (syn_csi R)) (syn_cpw1 (syn_crn R))) := by
  let proofSupport : Finset Var := R.fv
  have p0000 :=
    @g_cnvsi R
  have p0001 :=
    @g_dmeqi (syn_ccnv (syn_csi R)) (syn_csi (syn_ccnv R)) p0000
  have p0002 :=
    @g_dmsi (syn_ccnv R)
  have p0003 :=
    @g_eqtri (syn_cdm (syn_ccnv (syn_csi R))) (syn_cdm (syn_csi (syn_ccnv R))) (syn_cpw1 (syn_cdm (syn_ccnv R))) p0001 p0002
  have p0004 :=
    @g_dfrn4 (syn_csi R)
  have p0005 :=
    @g_dfrn4 R
  have p0006 :=
    @g_pw1eq (syn_crn R) (syn_cdm (syn_ccnv R))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_cdm (syn_ccnv (syn_csi R))) (syn_cpw1 (syn_cdm (syn_ccnv R))) (syn_crn (syn_csi R)) (syn_cpw1 (syn_crn R)) p0003 p0004 p0007
  exact p0008

noncomputable def g_op1std
    (A : Class) (B : Class) (C : Class) (hyp_op1st_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_op1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq C (syn_cop A B)) (.classEq (syn_cfv (syn_c1st) C) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_fveq2 C (syn_cop A B) (syn_c1st)
  have p0001 :=
    @g_opfv1st A B hyp_op1st_1 hyp_op1st_2
  have p0002 :=
    @g_syl6eq (.classEq C (syn_cop A B)) (syn_cfv (syn_c1st) C) (syn_cfv (syn_c1st) (syn_cop A B)) A p0000 p0001
  exact p0002

noncomputable def g_op2ndd
    (A : Class) (B : Class) (C : Class) (hyp_op1st_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_op1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq C (syn_cop A B)) (.classEq (syn_cfv (syn_c2nd) C) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_fveq2 C (syn_cop A B) (syn_c2nd)
  have p0001 :=
    @g_opfv2nd A B hyp_op1st_1 hyp_op1st_2
  have p0002 :=
    @g_syl6eq (.classEq C (syn_cop A B)) (syn_cfv (syn_c2nd) C) (syn_cfv (syn_c2nd) (syn_cop A B)) B p0000 p0001
  exact p0002

noncomputable def g_oveq1
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_co A F C) (syn_co B F C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_opeq1 A B C
  have p0001 :=
    @g_fveq2d (.classEq A B) (syn_cop A C) (syn_cop B C) F p0000
  have p0002 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co A F C)))
  have p0003 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co B F C)))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cfv F (syn_cop A C)) (syn_cfv F (syn_cop B C)) (syn_co A F C) (syn_co B F C) p0001 p0002 p0003
  exact p0004

noncomputable def g_oveq2
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_co C F A) (syn_co C F B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_opeq2 A B C
  have p0001 :=
    @g_fveq2d (.classEq A B) (syn_cop C A) (syn_cop C B) F p0000
  have p0002 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co C F A)))
  have p0003 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co C F B)))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cfv F (syn_cop C A)) (syn_cfv F (syn_cop C B)) (syn_co C F A) (syn_co C F B) p0001 p0002 p0003
  exact p0004

noncomputable def g_oveq12
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq A B) (.classEq C D)) (.classEq (syn_co A F C) (syn_co B F D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  have p0000 :=
    @g_oveq1 A B C F
  have p0001 :=
    @g_oveq2 C D B F
  have p0002 :=
    @g_sylan9eq (.classEq A B) (.classEq C D) (syn_co A F C) (syn_co B F C) (syn_co B F D) p0000 p0001
  exact p0002

noncomputable def g_oveq2d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (F : Class) (hyp_oveq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_co C F A) (syn_co C F B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_oveq2 A B C F
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_co C F A) (syn_co C F B)) hyp_oveq1d_1 p0000
  exact p0001

noncomputable def g_ovex
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.classMem (syn_co A F B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co A F B)))
  have p0001 :=
    @g_fvex (syn_cop A B) F
  have p0002 :=
    @g_eqeltri (syn_co A F B) (syn_cfv F (syn_cop A B)) (syn_cvv) p0000 p0001
  exact p0002

#print axioms g_ovex

end NFChoice.DirectNominalPrf.WPPReplay
