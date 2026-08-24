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
import NominalWPPReplayChunk016Compact001Part012

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

noncomputable def g_wedifleastssndv
    (x : Var) (y : Var) (C : Class) (D : Class) (R : Class) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) (hyp_wedifleastssndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wedifleastssndv_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wrex x D (.neg (.classMem (.cv x) C))) (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) C)) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : x ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.neg (.classMem (.cv y) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wrex x D (.neg (.classMem (.cv x) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, (Ne.symm dv_x_y), dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_wrex x D (.neg (.classMem (.cv x) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_ne_x, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Wff.neg (.classMem (.cv x) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Wff.neg (.classMem (.cv x) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.neg (.classMem (.cv z) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0015 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0016 : z ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((Wff.imp (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, fresh_z_not_C, fresh_z_ne_y, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ ((syn_cdif D C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_D, fresh_w_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((syn_cima R (syn_csn (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_R, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : w ∉ ((syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_D, fresh_w_ne_z, fresh_w_not_C, fresh_w_ne_y, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_notab (.classMem (.cv x) C) x
  have p0001 :=
    @g_abid2 x C dv_cache_0001
  have p0002 :=
    @g_difeq2i (.cab x (.classMem (.cv x) C)) C (syn_cvv) p0001
  have p0003 :=
    @g_eqtri (.cab x (.neg (.classMem (.cv x) C))) (syn_cdif (syn_cvv) (.cab x (.classMem (.cv x) C))) (syn_cdif (syn_cvv) C) p0000 p0002
  have p0004 :=
    @g_vvex
  have p0005 :=
    @g_difex (syn_cvv) C p0004 hyp_wedifleastssndv_2
  have p0006 :=
    @g_eqeltri (.cab x (.neg (.classMem (.cv x) C))) (syn_cdif (syn_cvv) C) (syn_cvv) p0003 p0005
  have p0007 :=
    @g_eleq1 (.cv x) (.cv y) C
  have p0008 :=
    @g_notbid (.classEq (.cv x) (.cv y)) (.classMem (.cv x) C) (.classMem (.cv y) C) p0007
  have p0009 :=
    @g_eleq1 (.cv x) (.cv z) C
  have p0010 :=
    @g_notbid (.classEq (.cv x) (.cv z)) (.classMem (.cv x) C) (.classMem (.cv z) C) p0009
  have p0011 :=
    @g_a1i (syn_wbr R (syn_cwe) D) (syn_wrex x D (.neg (.classMem (.cv x) C))) hyp_wedifleastssndv_1
  have p0012 :=
    @g_id (syn_wrex x D (.neg (.classMem (.cv x) C)))
  have p0013_e01_recanon : Nominal.NPrf (.imp (.objEq x y) (syn_wb (.neg (.classMem (.cv x) C)) (.neg (.classMem (.cv y) C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0008
  have p0013_e02_recanon : Nominal.NPrf (.imp (.objEq x z) (syn_wb (.neg (.classMem (.cv x) C)) (.neg (.classMem (.cv z) C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0010
  have p0013 :=
    @g_weds (syn_wrex x D (.neg (.classMem (.cv x) C))) (.neg (.classMem (.cv x) C)) (.neg (.classMem (.cv y) C)) (.neg (.classMem (.cv z) C)) x y z D R dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0006 p0013_e01_recanon p0013_e02_recanon p0011 p0012
  have p0014 :=
    @g_simpl (.neg (.classMem (.cv y) C)) (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
  have p0015 :=
    @g_simpr (.neg (.classMem (.cv y) C)) (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))
  have p0016 :=
    @g_simpr (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))
  have p0017 :=
    @g_eldif (.cv w) D C
  have p0018 :=
    @g_sylib (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))) (.classMem (.cv w) (syn_cdif D C)) (syn_wa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))) p0016 p0017
  have p0019 :=
    @g_simpr (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))
  have p0020 :=
    @g_syl (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))) (syn_wa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))) (.neg (.classMem (.cv w) C)) p0018 p0019
  have p0021 :=
    @g_simpr (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))
  have p0022 :=
    @g_eldif (.cv w) D C
  have p0023 :=
    @g_sylib (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))) (.classMem (.cv w) (syn_cdif D C)) (syn_wa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))) p0021 p0022
  have p0024 :=
    @g_simpl (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))
  have p0025 :=
    @g_syl (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))) (syn_wa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))) (.classMem (.cv w) D) p0023 p0024
  have p0026 :=
    @g_simpl (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))
  have p0027 :=
    @g_jca (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))) (.classMem (.cv w) D) (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) p0025 p0026
  have p0028 :=
    @g_eleq1 (.cv z) (.cv w) C
  have p0029 :=
    @g_notbid (.classEq (.cv z) (.cv w)) (.classMem (.cv z) C) (.classMem (.cv w) C) p0028
  have p0030 :=
    @g_breq2 (.cv z) (.cv w) (.cv y) R
  have p0031 :=
    @g_imbi12d (.classEq (.cv z) (.cv w)) (.neg (.classMem (.cv z) C)) (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv z)) (syn_wbr (.cv y) R (.cv w)) p0029 p0030
  have p0032 :=
    @g_rspcva (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))) (.imp (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv w))) z (.cv w) D dv_cache_0016 dv_cache_0004 dv_cache_0017 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))) (syn_wa (.classMem (.cv w) D) (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))) (.imp (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv w))) p0027 p0032
  have p0034 :=
    @g_mpd (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))) (.neg (.classMem (.cv w) C)) (syn_wbr (.cv y) R (.cv w)) p0020 p0033
  have p0035 :=
    @g_elimasn R (.cv y) (.cv w)
  have p0036 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv y) R (.cv w))))
  have p0037 :=
    @g_bitr4i (.classMem (.cv w) (syn_cima R (syn_csn (.cv y)))) (.classMem (syn_cop (.cv y) (.cv w)) R) (syn_wbr (.cv y) R (.cv w)) p0035 p0036
  have p0038 :=
    @g_sylibr (syn_wa (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C))) (syn_wbr (.cv y) R (.cv w)) (.classMem (.cv w) (syn_cima R (syn_csn (.cv y)))) p0034 p0037
  have p0039 :=
    @g_ex (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (.classMem (.cv w) (syn_cdif D C)) (.classMem (.cv w) (syn_cima R (syn_csn (.cv y)))) p0038
  have p0040 :=
    @g_ssrdv (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) w (syn_cdif D C) (syn_cima R (syn_csn (.cv y))) dv_cache_0018 dv_cache_0019 dv_cache_0020 p0039
  have p0041 :=
    @g_syl (syn_wa (.neg (.classMem (.cv y) C)) (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))) (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y)))) p0015 p0040
  have p0042 :=
    @g_jca (syn_wa (.neg (.classMem (.cv y) C)) (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))) (.neg (.classMem (.cv y) C)) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y)))) p0014 p0041
  have p0043 :=
    @g_reximi (syn_wa (.neg (.classMem (.cv y) C)) (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z))))) (syn_wa (.neg (.classMem (.cv y) C)) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y))))) y D p0042
  have p0044 :=
    @g_syl (syn_wrex x D (.neg (.classMem (.cv x) C))) (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) C)) (syn_wral z D (.imp (.neg (.classMem (.cv z) C)) (syn_wbr (.cv y) R (.cv z)))))) (syn_wrex y D (syn_wa (.neg (.classMem (.cv y) C)) (syn_wss (syn_cdif D C) (syn_cima R (syn_csn (.cv y)))))) p0013 p0043
  exact p0044

#print axioms g_wedifleastssndv

end NFChoice.DirectNominalPrf.WPPReplay
