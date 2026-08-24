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
import NominalWPPReplayChunk017Compact001Part005

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

noncomputable def g_siecsnndv
    (u : Var) (R : Class) (dv_R_u : u ∉ R.fv) :
    Nominal.NPrf (.classEq (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cpw1 (syn_cec (.cv u) R))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ R.fv
  let p : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_u_ne_p : u ≠ p :=
    Ne.symm fresh_p_ne_u
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p_ne_x : p ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_ne_y : p ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_p : y ≠ p :=
    Ne.symm fresh_p_ne_y
  have fresh_p_ne_z : p ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_p : z ≠ p :=
    Ne.symm fresh_p_ne_z
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((syn_csn (.cv u))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_csn (.cv u))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cec (.cv u) R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Wff.classEq (.cv p) (syn_csn (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, fresh_x_ne_u, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_u, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_cec (.cv u) R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Wff.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_u, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((syn_cec (syn_csn (.cv u)) (syn_csi R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_u, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((syn_cpw1 (syn_cec (.cv u) R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_u, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elec (.cv p) (syn_csn (.cv u)) (syn_csi R)
  have p0001 :=
    @g_biimpi (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) (syn_wbr (syn_csn (.cv u)) (syn_csi R) (.cv p)) p0000
  have p0002 :=
    @g_brsi x y (syn_csn (.cv u)) (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    @g_sylib (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) (syn_wbr (syn_csn (.cv u)) (syn_csi R) (.cv p)) (syn_wex x (syn_wex y (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))))) p0001 p0002
  have p0004 :=
    @g_simp3 (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0005 :=
    @g_simp1 (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0006 :=
    @g_vex u
  have p0007 :=
    @g_sneqr (.cv u) (.cv x) p0006
  have p0008 :=
    @g_syl (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv u) (.cv x)) p0005 p0007
  have p0009 :=
    @g_breq1d (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (.cv u) (.cv x) (.cv y) R p0008
  have p0010 :=
    @g_mpbird (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (.cv u) R (.cv y)) (syn_wbr (.cv x) R (.cv y)) p0004 p0009
  have p0011 :=
    @g_elec (.cv y) (.cv u) R
  have p0012 :=
    @g_sylibr (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (.cv u) R (.cv y)) (.classMem (.cv y) (syn_cec (.cv u) R)) p0010 p0011
  have p0013 :=
    @g_simp2 (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0014 :=
    @g_jca (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y))) p0012 p0013
  have p0015 :=
    @g_id (.classEq (.cv z) (.cv y))
  have p0016 :=
    @g_sneqd (.classEq (.cv z) (.cv y)) (.cv z) (.cv y) p0015
  have p0017 :=
    @g_eqeq2d (.classEq (.cv z) (.cv y)) (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv p) p0016
  have p0018 :=
    @g_rspcev (.classEq (.cv p) (syn_csn (.cv z))) (.classEq (.cv p) (syn_csn (.cv y))) z (.cv y) (syn_cec (.cv u) R) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0017
  have p0019 :=
    @g_syl (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))) (syn_wrex z (syn_cec (.cv u) R) (.classEq (.cv p) (syn_csn (.cv z)))) p0014 p0018
  have p0020 :=
    @g_elpw1 z (.cv p) (syn_cec (.cv u) R) dv_cache_0011 dv_cache_0009
  have p0021 :=
    @g_sylibr (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wrex z (syn_cec (.cv u) R) (.classEq (.cv p) (syn_csn (.cv z)))) (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) p0019 p0020
  have p0022 :=
    @g_exlimivv (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) x y dv_cache_0012 dv_cache_0013 p0021
  have p0023 :=
    @g_syl (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) (syn_wex x (syn_wex y (syn_w3a (.classEq (syn_csn (.cv u)) (syn_csn (.cv x))) (.classEq (.cv p) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))))) (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) p0003 p0022
  have p0024 :=
    @g_elpw1 y (.cv p) (syn_cec (.cv u) R) dv_cache_0004 dv_cache_0014
  have p0025 :=
    @g_biimpi (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) (syn_wrex y (syn_cec (.cv u) R) (.classEq (.cv p) (syn_csn (.cv y)))) p0024
  have p0026 :=
    @g_simpl (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))
  have p0027 :=
    @g_elec (.cv y) (.cv u) R
  have p0028 :=
    @g_sylib (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))) (.classMem (.cv y) (syn_cec (.cv u) R)) (syn_wbr (.cv u) R (.cv y)) p0026 p0027
  have p0029 :=
    @g_vex u
  have p0030 :=
    @g_vex y
  have p0031 :=
    @g_brsnsi (.cv u) (.cv y) R p0029 p0030
  have p0032 :=
    @g_sylibr (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))) (syn_wbr (.cv u) R (.cv y)) (syn_wbr (syn_csn (.cv u)) (syn_csi R) (syn_csn (.cv y))) p0028 p0031
  have p0033 :=
    @g_simpr (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))
  have p0034 :=
    @g_breq2d (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))) (.cv p) (syn_csn (.cv y)) (syn_csn (.cv u)) (syn_csi R) p0033
  have p0035 :=
    @g_mpbird (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))) (syn_wbr (syn_csn (.cv u)) (syn_csi R) (.cv p)) (syn_wbr (syn_csn (.cv u)) (syn_csi R) (syn_csn (.cv y))) p0032 p0034
  have p0036 :=
    @g_elec (.cv p) (syn_csn (.cv u)) (syn_csi R)
  have p0037 :=
    @g_sylibr (syn_wa (.classMem (.cv y) (syn_cec (.cv u) R)) (.classEq (.cv p) (syn_csn (.cv y)))) (syn_wbr (syn_csn (.cv u)) (syn_csi R) (.cv p)) (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) p0035 p0036
  have p0038 :=
    @g_rexlimiva (.classEq (.cv p) (syn_csn (.cv y))) (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) y (syn_cec (.cv u) R) dv_cache_0015 p0037
  have p0039 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) (syn_wrex y (syn_cec (.cv u) R) (.classEq (.cv p) (syn_csn (.cv y)))) (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) p0025 p0038
  have p0040 :=
    @g_impbii (.classMem (.cv p) (syn_cec (syn_csn (.cv u)) (syn_csi R))) (.classMem (.cv p) (syn_cpw1 (syn_cec (.cv u) R))) p0023 p0039
  have p0041 :=
    @g_eqriv p (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cpw1 (syn_cec (.cv u) R)) dv_cache_0016 dv_cache_0017 p0040
  exact p0041

noncomputable def g_siecsnclndv
    (C : Class) (R : Class) :
    Nominal.NPrf (.imp (.classMem C (syn_cvv)) (.classEq (syn_cec (syn_csn C) (syn_csi R)) (syn_cpw1 (syn_cec C R)))) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (R).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((Wff.classEq (syn_cec (syn_csn C) (syn_csi R)) (syn_cpw1 (syn_cec C R)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((Wff.classMem C (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem C (syn_cvv))
  have p0001 :=
    @g_simpr (.classMem C (syn_cvv)) (.classEq (.cv u) C)
  have p0002 :=
    @g_sneq (.cv u) C
  have p0003 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C)) (.classEq (.cv u) C) (.classEq (syn_csn (.cv u)) (syn_csn C)) p0001 p0002
  have p0004 :=
    @g_eceq1 (syn_csn (.cv u)) (syn_csn C) (syn_csi R)
  have p0005 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C)) (.classEq (syn_csn (.cv u)) (syn_csn C)) (.classEq (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cec (syn_csn C) (syn_csi R))) p0003 p0004
  have p0006 :=
    @g_simpr (.classMem C (syn_cvv)) (.classEq (.cv u) C)
  have p0007 :=
    @g_eceq1 (.cv u) C R
  have p0008 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C)) (.classEq (.cv u) C) (.classEq (syn_cec (.cv u) R) (syn_cec C R)) p0006 p0007
  have p0009 :=
    @g_pw1eq (syn_cec (.cv u) R) (syn_cec C R)
  have p0010 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C)) (.classEq (syn_cec (.cv u) R) (syn_cec C R)) (.classEq (syn_cpw1 (syn_cec (.cv u) R)) (syn_cpw1 (syn_cec C R))) p0008 p0009
  have p0011 :=
    @g_eqeq12d (syn_wa (.classMem C (syn_cvv)) (.classEq (.cv u) C)) (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cec (syn_csn C) (syn_csi R)) (syn_cpw1 (syn_cec (.cv u) R)) (syn_cpw1 (syn_cec C R)) p0005 p0010
  have p0012 :=
    @g_siecsnndv u R dv_cache_0001
  have p0013 :=
    @g_a1i (.classEq (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cpw1 (syn_cec (.cv u) R))) (.classMem C (syn_cvv)) p0012
  have p0014 :=
    @g_vtocld (.classMem C (syn_cvv)) (.classEq (syn_cec (syn_csn (.cv u)) (syn_csi R)) (syn_cpw1 (syn_cec (.cv u) R))) (.classEq (syn_cec (syn_csn C) (syn_csi R)) (syn_cpw1 (syn_cec C R))) u C (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000 p0011 p0013
  exact p0014

noncomputable def g_f1oclassimfreeclndv
    (v : Var) (A : Class) (B : Class) (Q : Class) (S : Class) (T : Class) (F : Class) (dv_A_v : v ∉ A.fv) (dv_B_v : v ∉ B.fv) (dv_F_v : v ∉ F.fv) (dv_Q_v : v ∉ Q.fv) (dv_S_v : v ∉ S.fv) (dv_T_v : v ∉ T.fv) (hyp_f1oclassimfreeclndv_1 : Nominal.NPrf (syn_wf1o F A B)) (hyp_f1oclassimfreeclndv_2 : Nominal.NPrf (syn_wss (syn_cec Q T) A)) (hyp_f1oclassimfreeclndv_3 : Nominal.NPrf (syn_wss (syn_cec (syn_cfv F Q) S) B)) (hyp_f1oclassimfreeclndv_4 : Nominal.NPrf (syn_wral v A (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v)))))) (hyp_f1oclassimfreeclndv_5 : Nominal.NPrf (.classMem Q A)) :
    Nominal.NPrf (.classEq (syn_cima F (syn_cec Q T)) (syn_cec (syn_cfv F Q) S)) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ A.fv ∪ B.fv ∪ Q.fv ∪ S.fv ∪ T.fv ∪ F.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_Q : z ∉ Q.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_T : z ∉ T.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ ((syn_cfv (syn_ccnv F) (.cv z))).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_z, dv_F_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((syn_wb (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_Q_v, fresh_v_ne_z, dv_F_v, dv_T_v, dv_S_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_cima F (syn_cec Q T))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, fresh_z_not_Q, fresh_z_not_T, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cec (syn_cfv F Q) S)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_Q, fresh_z_not_F, fresh_z_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem (.cv z) (syn_cima F (syn_cec Q T)))
  have p0001 :=
    @g_imassrn F (syn_cec Q T)
  have p0002 :=
    @g_f1of A B F
  have p0003 :=
    Nominal.mp hyp_f1oclassimfreeclndv_1 p0002
  have p0004 :=
    @g_frn A B F
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wss (syn_cima F (syn_cec Q T)) (syn_crn F)) (syn_wss (syn_crn F) B) p0001 p0005
  have p0007 :=
    @g_sstr (syn_cima F (syn_cec Q T)) (syn_crn F) B
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_sseli (syn_cima F (syn_cec Q T)) B (.cv z) p0008
  have p0010 :=
    @g_a1i (syn_wf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0011 :=
    @g_id (.classMem (.cv z) B)
  have p0012 :=
    @g_jca (.classMem (.cv z) B) (syn_wf1o F A B) (.classMem (.cv z) B) p0010 p0011
  have p0013 :=
    @g_f1ocnvfv2 A B (.cv z) F
  have p0014 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B)) (.classEq (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z)) p0012 p0013
  have p0015 :=
    @g_eleq1d (.classMem (.cv z) B) (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z) (syn_cima F (syn_cec Q T)) p0014
  have p0016 :=
    @g_f1of1 A B F
  have p0017 :=
    Nominal.mp hyp_f1oclassimfreeclndv_1 p0016
  have p0018 :=
    @g_a1i (syn_wf1 F A B) (.classMem (.cv z) B) p0017
  have p0019 :=
    @g_a1i (syn_wf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0020 :=
    @g_id (.classMem (.cv z) B)
  have p0021 :=
    @g_jca (.classMem (.cv z) B) (syn_wf1o F A B) (.classMem (.cv z) B) p0019 p0020
  have p0022 :=
    @g_f1ocnvdm A B (.cv z) F
  have p0023 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B)) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) p0021 p0022
  have p0024 :=
    @g_a1i (syn_wss (syn_cec Q T) A) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_2
  have p0025 :=
    @g_n_3jca (.classMem (.cv z) B) (syn_wf1 F A B) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) (syn_wss (syn_cec Q T) A) p0018 p0023 p0024
  have p0026 :=
    @g_f1elima A B F (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)
  have p0027 :=
    @g_syl (.classMem (.cv z) B) (syn_w3a (syn_wf1 F A B) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) (syn_wss (syn_cec Q T) A)) (syn_wb (.classMem (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (syn_cima F (syn_cec Q T))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T))) p0025 p0026
  have p0028 :=
    @g_bitr3d (.classMem (.cv z) B) (.classMem (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)) p0015 p0027
  have p0029 :=
    @g_elec (syn_cfv (syn_ccnv F) (.cv z)) Q T
  have p0030 :=
    @g_a1i (syn_wb (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)) (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z)))) (.classMem (.cv z) B) p0029
  have p0031 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)) (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) p0028 p0030
  have p0032 :=
    @g_a1i (syn_wral v A (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))))) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_4
  have p0033 :=
    @g_a1i (syn_wf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0034 :=
    @g_id (.classMem (.cv z) B)
  have p0035 :=
    @g_jca (.classMem (.cv z) B) (syn_wf1o F A B) (.classMem (.cv z) B) p0033 p0034
  have p0036 :=
    @g_f1ocnvdm A B (.cv z) F
  have p0037 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B)) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) p0035 p0036
  have p0038 :=
    @g_jca (.classMem (.cv z) B) (syn_wral v A (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) p0032 p0037
  have p0039 :=
    @g_id (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z)))
  have p0040 :=
    @g_breq2d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (.cv v) (syn_cfv (syn_ccnv F) (.cv z)) Q T p0039
  have p0041 :=
    @g_id (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z)))
  have p0042 :=
    @g_fveq2d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (.cv v) (syn_cfv (syn_ccnv F) (.cv z)) F p0041
  have p0043 :=
    @g_breq2d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (syn_cfv F (.cv v)) (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (syn_cfv F Q) S p0042
  have p0044 :=
    @g_bibi12d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr Q T (.cv v)) (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))) p0040 p0043
  have p0045 :=
    @g_rspccva (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v)))) (syn_wb (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))))) v (syn_cfv (syn_ccnv F) (.cv z)) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0044
  have p0046 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wral v A (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A)) (syn_wb (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))))) p0038 p0045
  have p0047 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))) p0031 p0046
  have p0048 :=
    @g_a1i (syn_wf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0049 :=
    @g_id (.classMem (.cv z) B)
  have p0050 :=
    @g_jca (.classMem (.cv z) B) (syn_wf1o F A B) (.classMem (.cv z) B) p0048 p0049
  have p0051 :=
    @g_f1ocnvfv2 A B (.cv z) F
  have p0052 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B)) (.classEq (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z)) p0050 p0051
  have p0053 :=
    @g_breq2d (.classMem (.cv z) B) (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z) (syn_cfv F Q) S p0052
  have p0054 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))) (syn_wbr (syn_cfv F Q) S (.cv z)) p0047 p0053
  have p0055 :=
    @g_elec (.cv z) (syn_cfv F Q) S
  have p0056 :=
    @g_a1i (syn_wb (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) (syn_wbr (syn_cfv F Q) S (.cv z))) (.classMem (.cv z) B) p0055
  have p0057 :=
    @g_bicomd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) (syn_wbr (syn_cfv F Q) S (.cv z)) p0056
  have p0058 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (syn_wbr (syn_cfv F Q) S (.cv z)) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) p0054 p0057
  have p0059 :=
    @g_syl (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) B) (syn_wb (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S))) p0009 p0058
  have p0060 :=
    @g_mpbid (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) p0000 p0059
  have p0061 :=
    @g_id (.classMem (.cv z) (syn_cec (syn_cfv F Q) S))
  have p0062 :=
    @g_sseli (syn_cec (syn_cfv F Q) S) B (.cv z) hyp_f1oclassimfreeclndv_3
  have p0063 :=
    @g_a1i (syn_wf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0064 :=
    @g_id (.classMem (.cv z) B)
  have p0065 :=
    @g_jca (.classMem (.cv z) B) (syn_wf1o F A B) (.classMem (.cv z) B) p0063 p0064
  have p0066 :=
    @g_f1ocnvfv2 A B (.cv z) F
  have p0067 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B)) (.classEq (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z)) p0065 p0066
  have p0068 :=
    @g_eleq1d (.classMem (.cv z) B) (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z) (syn_cima F (syn_cec Q T)) p0067
  have p0069 :=
    @g_f1of1 A B F
  have p0070 :=
    Nominal.mp hyp_f1oclassimfreeclndv_1 p0069
  have p0071 :=
    @g_a1i (syn_wf1 F A B) (.classMem (.cv z) B) p0070
  have p0072 :=
    @g_a1i (syn_wf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0073 :=
    @g_id (.classMem (.cv z) B)
  have p0074 :=
    @g_jca (.classMem (.cv z) B) (syn_wf1o F A B) (.classMem (.cv z) B) p0072 p0073
  have p0075 :=
    @g_f1ocnvdm A B (.cv z) F
  have p0076 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B)) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) p0074 p0075
  have p0077 :=
    @g_a1i (syn_wss (syn_cec Q T) A) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_2
  have p0078 :=
    @g_n_3jca (.classMem (.cv z) B) (syn_wf1 F A B) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) (syn_wss (syn_cec Q T) A) p0071 p0076 p0077
  have p0079 :=
    @g_f1elima A B F (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)
  have p0080 :=
    @g_syl (.classMem (.cv z) B) (syn_w3a (syn_wf1 F A B) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) (syn_wss (syn_cec Q T) A)) (syn_wb (.classMem (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (syn_cima F (syn_cec Q T))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T))) p0078 p0079
  have p0081 :=
    @g_bitr3d (.classMem (.cv z) B) (.classMem (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)) p0068 p0080
  have p0082 :=
    @g_elec (syn_cfv (syn_ccnv F) (.cv z)) Q T
  have p0083 :=
    @g_a1i (syn_wb (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)) (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z)))) (.classMem (.cv z) B) p0082
  have p0084 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) (syn_cec Q T)) (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) p0081 p0083
  have p0085 :=
    @g_a1i (syn_wral v A (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))))) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_4
  have p0086 :=
    @g_a1i (syn_wf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0087 :=
    @g_id (.classMem (.cv z) B)
  have p0088 :=
    @g_jca (.classMem (.cv z) B) (syn_wf1o F A B) (.classMem (.cv z) B) p0086 p0087
  have p0089 :=
    @g_f1ocnvdm A B (.cv z) F
  have p0090 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B)) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) p0088 p0089
  have p0091 :=
    @g_jca (.classMem (.cv z) B) (syn_wral v A (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A) p0085 p0090
  have p0092 :=
    @g_id (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z)))
  have p0093 :=
    @g_breq2d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (.cv v) (syn_cfv (syn_ccnv F) (.cv z)) Q T p0092
  have p0094 :=
    @g_id (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z)))
  have p0095 :=
    @g_fveq2d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (.cv v) (syn_cfv (syn_ccnv F) (.cv z)) F p0094
  have p0096 :=
    @g_breq2d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (syn_cfv F (.cv v)) (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (syn_cfv F Q) S p0095
  have p0097 :=
    @g_bibi12d (.classEq (.cv v) (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr Q T (.cv v)) (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))) p0093 p0096
  have p0098 :=
    @g_rspccva (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v)))) (syn_wb (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))))) v (syn_cfv (syn_ccnv F) (.cv z)) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0097
  have p0099 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wral v A (syn_wb (syn_wbr Q T (.cv v)) (syn_wbr (syn_cfv F Q) S (syn_cfv F (.cv v))))) (.classMem (syn_cfv (syn_ccnv F) (.cv z)) A)) (syn_wb (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))))) p0091 p0098
  have p0100 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (syn_wbr Q T (syn_cfv (syn_ccnv F) (.cv z))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))) p0084 p0099
  have p0101 :=
    @g_a1i (syn_wf1o F A B) (.classMem (.cv z) B) hyp_f1oclassimfreeclndv_1
  have p0102 :=
    @g_id (.classMem (.cv z) B)
  have p0103 :=
    @g_jca (.classMem (.cv z) B) (syn_wf1o F A B) (.classMem (.cv z) B) p0101 p0102
  have p0104 :=
    @g_f1ocnvfv2 A B (.cv z) F
  have p0105 :=
    @g_syl (.classMem (.cv z) B) (syn_wa (syn_wf1o F A B) (.classMem (.cv z) B)) (.classEq (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z)) p0103 p0104
  have p0106 :=
    @g_breq2d (.classMem (.cv z) B) (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z))) (.cv z) (syn_cfv F Q) S p0105
  have p0107 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (syn_wbr (syn_cfv F Q) S (syn_cfv F (syn_cfv (syn_ccnv F) (.cv z)))) (syn_wbr (syn_cfv F Q) S (.cv z)) p0100 p0106
  have p0108 :=
    @g_elec (.cv z) (syn_cfv F Q) S
  have p0109 :=
    @g_a1i (syn_wb (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) (syn_wbr (syn_cfv F Q) S (.cv z))) (.classMem (.cv z) B) p0108
  have p0110 :=
    @g_bicomd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) (syn_wbr (syn_cfv F Q) S (.cv z)) p0109
  have p0111 :=
    @g_bitrd (.classMem (.cv z) B) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (syn_wbr (syn_cfv F Q) S (.cv z)) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) p0107 p0110
  have p0112 :=
    @g_syl (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) (.classMem (.cv z) B) (syn_wb (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S))) p0062 p0111
  have p0113 :=
    @g_mpbird (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) p0061 p0112
  have p0114 :=
    @g_impbii (.classMem (.cv z) (syn_cima F (syn_cec Q T))) (.classMem (.cv z) (syn_cec (syn_cfv F Q) S)) p0060 p0113
  have p0115 :=
    @g_eqriv z (syn_cima F (syn_cec Q T)) (syn_cec (syn_cfv F Q) S) dv_cache_0004 dv_cache_0005 p0114
  exact p0115

noncomputable def g_hnsicodemapkernelclndv
    (A : Class) (Q : Class) (r : Var) (dv_A_r : r ∉ A.fv) (dv_Q_r : r ∉ Q.fv) :
    Nominal.NPrf (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (.imp (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r)))))) := by
  let proofSupport : Finset Var := A.fv ∪ Q.fv ∪ ({r} : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_r : q ≠ r := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0004 : q ∉ (Q).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((Wff.imp (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_r, fresh_q_not_A, fresh_q_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_biid (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0001 :=
    @g_a1i (syn_wb (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))) (.classEq (.cv q) Q) p0000
  have p0002 :=
    @g_id (.classEq (.cv q) Q)
  have p0003 :=
    @g_breq1d (.classEq (.cv q) Q) (.cv q) Q (.cv r) (syn_csi (syn_chwniso A)) p0002
  have p0004 :=
    @g_id (.classEq (.cv q) Q)
  have p0005 :=
    @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsicodemap A) p0004
  have p0006 :=
    @g_breq1d (.classEq (.cv q) Q) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) Q) (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A)) p0005
  have p0007 :=
    @g_bibi12d (.classEq (.cv q) Q) (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))) p0003 p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv q) Q) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) p0001 p0007
  have p0009 :=
    @g_hnsicodemapkernelndv A r q dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0010 :=
    @g_ex (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) p0009
  have p0011 :=
    @g_vtoclga (.imp (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.imp (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))))) q Q (syn_cpw1 (syn_chwcn A)) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0008 p0010
  exact p0011

noncomputable def g_hnsicodemapclassimclndv
    (A : Class) (Q : Class) (hyp_hnsicodemapclassimclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_hnsicodemapclassimclndv_2 : Nominal.NPrf (.classMem Q (syn_cpw1 (syn_chwcn A)))) :
    Nominal.NPrf (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)))) := by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_Q : r ∉ Q.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : r ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (Q).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_chwcn (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((syn_chnsicodemap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_chwniso (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_csi (syn_chwniso A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnsicodemapf1ondv A
  have p0001 :=
    @g_pw1argclcl (syn_chwcn A) Q
  have p0002 :=
    Nominal.mp hyp_hnsicodemapclassimclndv_2 p0001
  have p0003 :=
    @g_simpr (.classMem (syn_cuni Q) (syn_chwcn A)) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_eceq1 Q (syn_csn (syn_cuni Q)) (syn_csi (syn_chwniso A))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_pw1argclcl (syn_chwcn A) Q
  have p0008 :=
    Nominal.mp hyp_hnsicodemapclassimclndv_2 p0007
  have p0009 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_chwcn A)) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_elex (syn_cuni Q) (syn_chwcn A)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_siecsnclndv (syn_cuni Q) (syn_chwniso A)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_eqtri (syn_cec Q (syn_csi (syn_chwniso A))) (syn_cec (syn_csn (syn_cuni Q)) (syn_csi (syn_chwniso A))) (syn_cpw1 (syn_cec (syn_cuni Q) (syn_chwniso A))) p0006 p0014
  have p0016 :=
    @g_hwnisoerv A
  have p0017 :=
    @g_hwnisodm A
  have p0018 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A)) (.classMem A (syn_cvv)) p0017
  have p0019 :=
    @g_ecss (.classMem A (syn_cvv)) (syn_cuni Q) (syn_chwniso A) (syn_chwcn A) p0016 p0018
  have p0020 :=
    Nominal.mp hyp_hnsicodemapclassimclndv_1 p0019
  have p0021 :=
    @g_pw1ss (syn_cec (syn_cuni Q) (syn_chwniso A)) (syn_chwcn A)
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_eqsstri (syn_cec Q (syn_csi (syn_chwniso A))) (syn_cpw1 (syn_cec (syn_cuni Q) (syn_chwniso A))) (syn_cpw1 (syn_chwcn A)) p0015 p0022
  have p0024 :=
    @g_pw1exg A (syn_cvv)
  have p0025 :=
    Nominal.mp hyp_hnsicodemapclassimclndv_1 p0024
  have p0026 :=
    @g_hwnisoerv (syn_cpw1 A)
  have p0027 :=
    @g_hwnisodm (syn_cpw1 A)
  have p0028 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso (syn_cpw1 A))) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cpw1 A) (syn_cvv)) p0027
  have p0029 :=
    @g_ecss (.classMem (syn_cpw1 A) (syn_cvv)) (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_chwcn (syn_cpw1 A)) p0026 p0028
  have p0030 :=
    Nominal.mp p0025 p0029
  have p0031 :=
    @g_hnsicodemapkernelclndv A Q r dv_cache_0001 dv_cache_0002
  have p0032 :=
    Nominal.mp hyp_hnsicodemapclassimclndv_2 p0031
  have p0033 :=
    @g_rgen (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) r (syn_cpw1 (syn_chwcn A)) p0032
  have p0034 :=
    @g_f1oclassimfreeclndv r (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) Q (syn_chwniso (syn_cpw1 A)) (syn_csi (syn_chwniso A)) (syn_chnsicodemap A) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0006 dv_cache_0007 p0000 p0023 p0030 p0033 hyp_hnsicodemapclassimclndv_2
  exact p0034

#print axioms g_hnsicodemapclassimclndv

end NFChoice.DirectNominalPrf.WPPReplay
