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
import NominalWPPReplayChunk012BCompact001Part020

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

noncomputable def g_brtxp
    (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_ctxp R S) B) (syn_wex x (syn_wex y (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ S.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_S : w ∉ S.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_ccnv (syn_c1st))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_ccnv (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, (Ne.symm dv_x_y), dv_R_y, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_x_y, dv_S_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Wff.classEq B (syn_cop (.cv x) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_B, fresh_w_ne_x, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classEq B (syn_cop (.cv w) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, fresh_z_ne_w, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((Wff.classEq B (syn_cop (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ ((Wff.classEq B (syn_cop (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_B, fresh_w_ne_x, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : z ∉ ((syn_wa (.classEq B (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : w ∉ ((syn_wa (.classEq B (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_B, fresh_w_ne_x, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 :=
    @g_brin A B (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)
  have p0001 :=
    @g_brco x A B (syn_ccnv (syn_c1st)) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_brco y A B (syn_ccnv (syn_c2nd)) S dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0003 :=
    @g_anbi12i (syn_wbr A (syn_ccom (syn_ccnv (syn_c1st)) R) B) (syn_wex x (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))) (syn_wbr A (syn_ccom (syn_ccnv (syn_c2nd)) S) B) (syn_wex y (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))) p0001 p0002
  have p0004 :=
    @g_bitri (syn_wbr A (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)) B) (syn_wa (syn_wbr A (syn_ccom (syn_ccnv (syn_c1st)) R) B) (syn_wbr A (syn_ccom (syn_ccnv (syn_c2nd)) S) B)) (syn_wa (syn_wex x (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))) (syn_wex y (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)))) p0000 p0003
  have p0005 :=
    (by simpa [syn_ctxp] using (Nominal.classEqRefl (syn_ctxp R S)))
  have p0006 :=
    @g_breqi A B (syn_ctxp R S) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)) p0005
  have p0007 :=
    @g_eeanv (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)) (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)) x y dv_cache_0009 dv_cache_0010
  have p0008 :=
    @g_n_3bitr4i (syn_wbr A (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)) B) (syn_wa (syn_wex x (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))) (syn_wex y (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)))) (syn_wbr A (syn_ctxp R S) B) (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)) (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))))) p0004 p0006 p0007
  have p0009 :=
    @g_an4 (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B) (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)
  have p0010 :=
    @g_ancom (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))) (.classEq B (syn_cop (.cv x) (.cv y)))
  have p0011 :=
    @g_brcnv (.cv x) B (syn_c1st)
  have p0012 :=
    @g_vex x
  have p0013 :=
    @g_br1st z B (.cv x) dv_cache_0011 dv_cache_0012 p0012
  have p0014 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B) (syn_wbr B (syn_c1st) (.cv x)) (syn_wex z (.classEq B (syn_cop (.cv x) (.cv z)))) p0011 p0013
  have p0015 :=
    @g_brcnv (.cv y) B (syn_c2nd)
  have p0016 :=
    @g_vex y
  have p0017 :=
    @g_br2nd w B (.cv y) dv_cache_0013 dv_cache_0014 p0016
  have p0018 :=
    @g_bitri (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B) (syn_wbr B (syn_c2nd) (.cv y)) (syn_wex w (.classEq B (syn_cop (.cv w) (.cv y)))) p0015 p0017
  have p0019 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B) (syn_wex z (.classEq B (syn_cop (.cv x) (.cv z)))) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B) (syn_wex w (.classEq B (syn_cop (.cv w) (.cv y)))) p0014 p0018
  have p0020 :=
    @g_eeanv (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y))) z w dv_cache_0015 dv_cache_0016
  have p0021 :=
    @g_eqtr2 B (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))
  have p0022 :=
    @g_opth (.cv x) (.cv z) (.cv w) (.cv y)
  have p0023_e00_recanon : Nominal.NPrf (syn_wb (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))) (syn_wa (.objEq x w) (.objEq z y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0022
  have p0023 :=
    @g_simplbi (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))) (.objEq x w) (.objEq z y) p0023_e00_recanon
  have p0024_e00_recanon : Nominal.NPrf (.imp (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))) (.classEq (.cv x) (.cv w))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0023
  have p0024 :=
    @g_eqcomd (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))) (.cv x) (.cv w) p0024_e00_recanon
  have p0025 :=
    @g_opeq1d (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))) (.cv w) (.cv x) (.cv y) p0024
  have p0026 :=
    @g_syl (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y)))) (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))) (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y))) p0021 p0025
  have p0027 :=
    @g_eqeq1 B (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y))
  have p0028 :=
    @g_adantl (.classEq B (syn_cop (.cv w) (.cv y))) (syn_wb (.classEq B (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y)))) (.classEq B (syn_cop (.cv x) (.cv z))) p0027
  have p0029 :=
    @g_mpbird (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y)))) (.classEq B (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y))) p0026 p0028
  have p0030 :=
    @g_exlimivv (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y)))) (.classEq B (syn_cop (.cv x) (.cv y))) z w dv_cache_0017 dv_cache_0018 p0029
  have p0031 :=
    @g_opeq2 (.cv z) (.cv y) (.cv x)
  have p0032_e00_recanon : Nominal.NPrf (.imp (.objEq z y) (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0031
  have p0032 :=
    @g_eqeq2d (.objEq z y) (syn_cop (.cv x) (.cv z)) (syn_cop (.cv x) (.cv y)) B p0032_e00_recanon
  have p0033 :=
    @g_opeq1 (.cv w) (.cv x) (.cv y)
  have p0034_e00_recanon : Nominal.NPrf (.imp (.objEq w x) (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0033
  have p0034 :=
    @g_eqeq2d (.objEq w x) (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y)) B p0034_e00_recanon
  have p0035 :=
    @g_bi2anan9 (.objEq z y) (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv x) (.cv y))) (.objEq w x) (.classEq B (syn_cop (.cv w) (.cv y))) (.classEq B (syn_cop (.cv x) (.cv y))) p0032 p0034
  have p0036_e02_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv z) (.cv y)) (.classEq (.cv w) (.cv x))) (syn_wb (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y)))) (syn_wa (.classEq B (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0035
  have p0036 :=
    @g_spc2ev (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y)))) (syn_wa (.classEq B (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv x) (.cv y)))) z w (.cv y) (.cv x) dv_cache_0019 dv_cache_0014 dv_cache_0012 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 p0016 p0012 p0036_e02_recanon
  have p0037 :=
    @g_anidms (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wex z (syn_wex w (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y)))))) p0036
  have p0038 :=
    @g_impbii (syn_wex z (syn_wex w (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y)))))) (.classEq B (syn_cop (.cv x) (.cv y))) p0030 p0037
  have p0039 :=
    @g_n_3bitr2i (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)) (syn_wa (syn_wex z (.classEq B (syn_cop (.cv x) (.cv z)))) (syn_wex w (.classEq B (syn_cop (.cv w) (.cv y))))) (syn_wex z (syn_wex w (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y)))))) (.classEq B (syn_cop (.cv x) (.cv y))) p0019 p0020 p0038
  have p0040 :=
    @g_anbi2i (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)) (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))) p0039
  have p0041 :=
    @g_n_3anass (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))
  have p0042 :=
    @g_n_3bitr4i (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))) (.classEq B (syn_cop (.cv x) (.cv y)))) (syn_wa (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y)))) (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))) (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))) p0010 p0040 p0041
  have p0043 :=
    @g_bitri (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)) (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))) (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))) (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))) p0009 p0042
  have p0044 :=
    @g_n_2exbii (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)) (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))) (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))) x y p0043
  have p0045 :=
    @g_bitri (syn_wbr A (syn_ctxp R S) B) (syn_wex x (syn_wex y (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)) (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))))) (syn_wex x (syn_wex y (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))))) p0008 p0044
  exact p0045

noncomputable def g_txpexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_ctxp A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    (by simpa [syn_ctxp] using (Nominal.classEqRefl (syn_ctxp A B)))
  have p0001 :=
    @g_n_1stex
  have p0002 :=
    @g_cnvex (syn_c1st) p0001
  have p0003 :=
    @g_coexg (syn_ccnv (syn_c1st)) A (syn_cvv) V
  have p0004 :=
    @g_mpan (.classMem (syn_ccnv (syn_c1st)) (syn_cvv)) (.classMem A V) (.classMem (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_n_2ndex
  have p0006 :=
    @g_cnvex (syn_c2nd) p0005
  have p0007 :=
    @g_coexg (syn_ccnv (syn_c2nd)) B (syn_cvv) W
  have p0008 :=
    @g_mpan (.classMem (syn_ccnv (syn_c2nd)) (syn_cvv)) (.classMem B W) (.classMem (syn_ccom (syn_ccnv (syn_c2nd)) B) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_inexg (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c2nd)) B) (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl2an (.classMem A V) (.classMem (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_cvv)) (.classMem (syn_ccom (syn_ccnv (syn_c2nd)) B) (syn_cvv)) (.classMem (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c2nd)) B)) (syn_cvv)) (.classMem B W) p0004 p0008 p0009
  have p0011 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_ctxp A B) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c2nd)) B)) (syn_cvv) p0000 p0010
  exact p0011

noncomputable def g_txpex
    (A : Class) (B : Class) (hyp_txpex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_txpex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ctxp A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_txpexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_ctxp A B) (syn_cvv)) hyp_txpex_1 hyp_txpex_2 p0000
  exact p0001

noncomputable def g_elfix
    (A : Class) (R : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cfix R)) (syn_wbr A R A)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cin R (syn_cid))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_wbr (.cv x) R (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem A (syn_cfix R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfix, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wbr A R A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex A (syn_cfix R)
  have p0001 :=
    @g_brex A A R
  have p0002 :=
    @g_simpld (syn_wbr A R A) (.classMem A (syn_cvv)) (.classMem A (syn_cvv)) p0001
  have p0003 :=
    @g_eleq1 (.cv x) A (syn_cfix R)
  have p0004 :=
    @g_breq12 (.cv x) A (.cv x) A R
  have p0005 :=
    @g_anidms (.classEq (.cv x) A) (syn_wb (syn_wbr (.cv x) R (.cv x)) (syn_wbr A R A)) p0004
  have p0006 :=
    (by simpa [syn_cfix] using (Nominal.classEqRefl (syn_cfix R)))
  have p0007 :=
    @g_eleq2i (syn_cfix R) (syn_crn (syn_cin R (syn_cid))) (.cv x) p0006
  have p0008 :=
    @g_elrn y (.cv x) (syn_cin R (syn_cid)) dv_cache_0001 dv_cache_0002
  have p0009 :=
    @g_brin (.cv y) (.cv x) R (syn_cid)
  have p0010 :=
    @g_ancom (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) (syn_cid) (.cv x))
  have p0011 :=
    @g_vex x
  have p0012 :=
    @g_ideq (.cv y) (.cv x) p0011
  have p0013_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv y) (syn_cid) (.cv x)) (.objEq y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cid syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
    @g_anbi1i (syn_wbr (.cv y) (syn_cid) (.cv x)) (.objEq y x) (syn_wbr (.cv y) R (.cv x)) p0013_e00_recanon
  have p0014 :=
    @g_n_3bitri (syn_wbr (.cv y) (syn_cin R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_wa (syn_wbr (.cv y) (syn_cid) (.cv x)) (syn_wbr (.cv y) R (.cv x))) (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x))) p0009 p0010 p0013
  have p0015 :=
    @g_exbii (syn_wbr (.cv y) (syn_cin R (syn_cid)) (.cv x)) (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x))) y p0014
  have p0016 :=
    @g_bitri (.classMem (.cv x) (syn_crn (syn_cin R (syn_cid)))) (syn_wex y (syn_wbr (.cv y) (syn_cin R (syn_cid)) (.cv x))) (syn_wex y (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x)))) p0008 p0015
  have p0017 :=
    @g_breq1 (.cv y) (.cv x) (.cv x) R
  have p0018 :=
    @g_ceqsexv (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv x) R (.cv x)) y (.cv x) dv_cache_0001 dv_cache_0003 p0011 p0017
  have p0019_e02_recanon : Nominal.NPrf (syn_wb (syn_wex y (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x)))) (syn_wbr (.cv x) R (.cv x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0018
  have p0019 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cfix R)) (.classMem (.cv x) (syn_crn (syn_cin R (syn_cid)))) (syn_wex y (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x)))) (syn_wbr (.cv x) R (.cv x)) p0007 p0016 p0019_e02_recanon
  have p0020 :=
    @g_vtoclbg (.classMem (.cv x) (syn_cfix R)) (syn_wbr (.cv x) R (.cv x)) (.classMem A (syn_cfix R)) (syn_wbr A R A) x A (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0003 p0005 p0019
  have p0021 :=
    @g_pm5_21nii (.classMem A (syn_cfix R)) (.classMem A (syn_cvv)) (syn_wbr A R A) p0000 p0002 p0020
  exact p0021

noncomputable def g_fixexg
    (R : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem R V) (.classMem (syn_cfix R) (syn_cvv))) := by
  let proofSupport : Finset Var := R.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_cfix] using (Nominal.classEqRefl (syn_cfix R)))
  have p0001 :=
    @g_idex
  have p0002 :=
    @g_inexg R (syn_cid) V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem R V) (.classMem (syn_cid) (syn_cvv)) (.classMem (syn_cin R (syn_cid)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_rnexg (syn_cin R (syn_cid)) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem R V) (.classMem (syn_cin R (syn_cid)) (syn_cvv)) (.classMem (syn_crn (syn_cin R (syn_cid))) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (.classMem R V) (syn_cfix R) (syn_crn (syn_cin R (syn_cid))) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_fixex
    (R : Class) (hyp_fixex_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfix R) (syn_cvv)) := by
  let proofSupport : Finset Var := R.fv
  have p0000 :=
    @g_fixexg R (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_fixex_1 p0000
  exact p0001

noncomputable def g_op1st2nd
    (A : Class) (B : Class) (C : Class) (hyp_op1st2nd_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_op1st2nd_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wa (syn_wbr C (syn_c1st) A) (syn_wbr C (syn_c2nd) B)) (.classEq C (syn_cop A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.imp (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_B, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_br1st x C A dv_cache_0001 dv_cache_0002 hyp_op1st2nd_1
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_opbr2nd A (.cv x) B hyp_op1st2nd_1 p0001
  have p0003 :=
    @g_biimpi (syn_wbr (syn_cop A (.cv x)) (syn_c2nd) B) (.classEq (.cv x) B) p0002
  have p0004 :=
    @g_opeq2d (syn_wbr (syn_cop A (.cv x)) (syn_c2nd) B) (.cv x) B A p0003
  have p0005 :=
    @g_breq1 C (syn_cop A (.cv x)) B (syn_c2nd)
  have p0006 :=
    @g_eqeq1 C (syn_cop A (.cv x)) (syn_cop A B)
  have p0007 :=
    @g_imbi12d (.classEq C (syn_cop A (.cv x))) (syn_wbr C (syn_c2nd) B) (syn_wbr (syn_cop A (.cv x)) (syn_c2nd) B) (.classEq C (syn_cop A B)) (.classEq (syn_cop A (.cv x)) (syn_cop A B)) p0005 p0006
  have p0008 :=
    @g_mpbiri (.classEq C (syn_cop A (.cv x))) (.imp (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B))) (.imp (syn_wbr (syn_cop A (.cv x)) (syn_c2nd) B) (.classEq (syn_cop A (.cv x)) (syn_cop A B))) p0004 p0007
  have p0009 :=
    @g_exlimiv (.classEq C (syn_cop A (.cv x))) (.imp (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B))) x dv_cache_0003 p0008
  have p0010 :=
    @g_sylbi (syn_wbr C (syn_c1st) A) (syn_wex x (.classEq C (syn_cop A (.cv x)))) (.imp (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B))) p0000 p0009
  have p0011 :=
    @g_imp (syn_wbr C (syn_c1st) A) (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B)) p0010
  have p0012 :=
    @g_eqid A
  have p0013 :=
    @g_opbr1st A B A hyp_op1st2nd_1 hyp_op1st2nd_2
  have p0014 :=
    @g_mpbir (syn_wbr (syn_cop A B) (syn_c1st) A) (.classEq A A) p0012 p0013
  have p0015 :=
    @g_eqid B
  have p0016 :=
    @g_opbr2nd A B B hyp_op1st2nd_1 hyp_op1st2nd_2
  have p0017 :=
    @g_mpbir (syn_wbr (syn_cop A B) (syn_c2nd) B) (.classEq B B) p0015 p0016
  have p0018 :=
    @g_pm3_2i (syn_wbr (syn_cop A B) (syn_c1st) A) (syn_wbr (syn_cop A B) (syn_c2nd) B) p0014 p0017
  have p0019 :=
    @g_breq1 C (syn_cop A B) A (syn_c1st)
  have p0020 :=
    @g_breq1 C (syn_cop A B) B (syn_c2nd)
  have p0021 :=
    @g_anbi12d (.classEq C (syn_cop A B)) (syn_wbr C (syn_c1st) A) (syn_wbr (syn_cop A B) (syn_c1st) A) (syn_wbr C (syn_c2nd) B) (syn_wbr (syn_cop A B) (syn_c2nd) B) p0019 p0020
  have p0022 :=
    @g_mpbiri (.classEq C (syn_cop A B)) (syn_wa (syn_wbr C (syn_c1st) A) (syn_wbr C (syn_c2nd) B)) (syn_wa (syn_wbr (syn_cop A B) (syn_c1st) A) (syn_wbr (syn_cop A B) (syn_c2nd) B)) p0018 p0021
  have p0023 :=
    @g_impbii (syn_wa (syn_wbr C (syn_c1st) A) (syn_wbr C (syn_c2nd) B)) (.classEq C (syn_cop A B)) p0011 p0022
  exact p0023

noncomputable def g_otelins2
    (A : Class) (B : Class) (C : Class) (R : Class) (hyp_otelins2_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R)) (.classMem (syn_cop A C) R)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (syn_cop A C) R)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_C, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex (syn_cop A (syn_cop B C)) (syn_cins2 R)
  have p0001 :=
    @g_opexb A (syn_cop B C)
  have p0002 :=
    @g_simplbi (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem (syn_cop B C) (syn_cvv)) p0001
  have p0003 :=
    @g_syl (.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R)) (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (.classMem A (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_elex (syn_cop A C) R
  have p0005 :=
    @g_opexb A C
  have p0006 :=
    @g_simplbi (.classMem (syn_cop A C) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem C (syn_cvv)) p0005
  have p0007 :=
    @g_syl (.classMem (syn_cop A C) R) (.classMem (syn_cop A C) (syn_cvv)) (.classMem A (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_opeq1 (.cv x) A (syn_cop B C)
  have p0009 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cop B C)) (syn_cop A (syn_cop B C)) (syn_cins2 R) p0008
  have p0010 :=
    @g_opeq1 (.cv x) A C
  have p0011 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) C) (syn_cop A C) R p0010
  have p0012 :=
    @g_vex x
  have p0013 :=
    @g_opex (.cv x) B p0012 hyp_otelins2_1
  have p0014 :=
    (by simpa [syn_cins2] using (Nominal.classEqRefl (syn_cins2 R)))
  have p0015 :=
    @g_eleq2i (syn_cins2 R) (syn_ctxp (syn_cvv) R) (syn_cop (.cv x) (syn_cop B C)) p0014
  have p0016 :=
    @g_oteltxp (.cv x) B C (syn_cvv) R
  have p0017 :=
    @g_bitri (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins2 R)) (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_ctxp (syn_cvv) R)) (syn_wa (.classMem (syn_cop (.cv x) B) (syn_cvv)) (.classMem (syn_cop (.cv x) C) R)) p0015 p0016
  have p0018 :=
    @g_mpbiran (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins2 R)) (.classMem (syn_cop (.cv x) B) (syn_cvv)) (.classMem (syn_cop (.cv x) C) R) p0013 p0017
  have p0019 :=
    @g_vtoclbg (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins2 R)) (.classMem (syn_cop (.cv x) C) R) (.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R)) (.classMem (syn_cop A C) R) x A (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0009 p0011 p0018
  have p0020 :=
    @g_pm5_21nii (.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R)) (.classMem A (syn_cvv)) (.classMem (syn_cop A C) R) p0003 p0007 p0019
  exact p0020

#print axioms g_otelins2

end NFChoice.DirectNominalPrf.WPPReplay
