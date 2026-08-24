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
import NominalWPPReplayChunk016Compact001Part041

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

noncomputable def g_wppcandminfixedpivotsetdeddrfdv
    (z : Var) (C : Class) (D : Class) (R : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_R_n : n ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_n_z : n ≠ z) :
    Nominal.NPrf (.imp (.classMem F (syn_cvv)) (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({n} : Finset Var) ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_z : x ≠ z := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_z : y ≠ z := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_n : y ≠ n := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_y : n ≠ y :=
    Ne.symm fresh_y_ne_n
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_cimage (syn_ccnv F))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cimage (syn_ccnv F))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : z ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : n ∉ ((Wff.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : n ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : n ∉ ((syn_cif (.classMem F (syn_cvv)) F (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((syn_cif (.classMem F (syn_cvv)) F (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : n ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : n ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show n ≠ z from (by exact dv_n_z))
  have p0000 :=
    @g_biid (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
  have p0001 :=
    @g_a1i (syn_wb (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))) (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) p0000
  have p0002 :=
    @g_eqidd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0003 :=
    @g_id (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
  have p0004 :=
    @g_cnveqd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) p0003
  have p0005 :=
    @g_imaeq1d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_ccnv F) (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.cv x) p0004
  have p0006 :=
    @g_eqeq2d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cima (syn_ccnv F) (.cv x)) (syn_cima (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.cv x)) (.cv y) p0005
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_vex y
  have p0009 :=
    @g_brimage (.cv x) (.cv y) (syn_ccnv F) p0007 p0008
  have p0010 :=
    @g_vex x
  have p0011 :=
    @g_vex y
  have p0012 :=
    @g_brimage (.cv x) (.cv y) (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) p0010 p0011
  have p0013 :=
    @g_n_3bitr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.classEq (.cv y) (syn_cima (syn_ccnv F) (.cv x))) (.classEq (.cv y) (syn_cima (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.cv x))) (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y)) (syn_wbr (.cv x) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y)) p0006 p0009 p0012
  have p0014 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y))))
  have p0015 :=
    @g_bicomi (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv F))) p0014
  have p0016 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y))))
  have p0017 :=
    @g_bicomi (syn_wbr (.cv x) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))) p0016
  have p0018 :=
    @g_n_3bitr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y)) (syn_wbr (.cv x) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv F))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))) p0013 p0015 p0017
  have p0019 :=
    @g_eqrelrdv (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) x y (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0018
  have p0020 :=
    @g_eqidd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cima (syn_clec) (syn_csn C))
  have p0021 :=
    @g_jca (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))) (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn C))) p0019 p0020
  have p0022 :=
    @g_freceq12 (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn C))
  have p0023 :=
    @g_syl (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_wa (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))) (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn C)))) (.classEq (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C)))) p0021 p0022
  have p0024 :=
    @g_rneqd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C))) p0023
  have p0025 :=
    @g_unieqd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C)))) p0024
  have p0026 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach F C)))
  have p0027 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)))
  have p0028 :=
    @g_n_3eqtr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C))))) (syn_cwppreach F C) (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) p0025 p0026 p0027
  have p0029 :=
    @g_ineq12d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C) (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) p0002 p0028
  have p0030 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand F C)))
  have p0031 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)))
  have p0032 :=
    @g_n_3eqtr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C)) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)) (syn_cwppcand F C) (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) p0029 p0030 p0031
  have p0033 :=
    @g_eqidd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0034 :=
    @g_id (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
  have p0035 :=
    @g_cnveqd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) p0034
  have p0036 :=
    @g_imaeq1d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_ccnv F) (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.cv x) p0035
  have p0037 :=
    @g_eqeq2d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cima (syn_ccnv F) (.cv x)) (syn_cima (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.cv x)) (.cv y) p0036
  have p0038 :=
    @g_vex x
  have p0039 :=
    @g_vex y
  have p0040 :=
    @g_brimage (.cv x) (.cv y) (syn_ccnv F) p0038 p0039
  have p0041 :=
    @g_vex x
  have p0042 :=
    @g_vex y
  have p0043 :=
    @g_brimage (.cv x) (.cv y) (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) p0041 p0042
  have p0044 :=
    @g_n_3bitr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.classEq (.cv y) (syn_cima (syn_ccnv F) (.cv x))) (.classEq (.cv y) (syn_cima (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.cv x))) (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y)) (syn_wbr (.cv x) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y)) p0037 p0040 p0043
  have p0045 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y))))
  have p0046 :=
    @g_bicomi (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv F))) p0045
  have p0047 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y))))
  have p0048 :=
    @g_bicomi (syn_wbr (.cv x) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))) p0047
  have p0049 :=
    @g_n_3bitr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y)) (syn_wbr (.cv x) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv F))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))) p0044 p0046 p0048
  have p0050 :=
    @g_eqrelrdv (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) x y (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0049
  have p0051 :=
    @g_eqidd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cima (syn_clec) (syn_csn C))
  have p0052 :=
    @g_jca (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))) (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn C))) p0050 p0051
  have p0053 :=
    @g_freceq12 (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn C))
  have p0054 :=
    @g_syl (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_wa (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))) (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn C)))) (.classEq (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C)))) p0052 p0053
  have p0055 :=
    @g_rneqd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C))) p0054
  have p0056 :=
    @g_unieqd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C)))) p0055
  have p0057 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach F C)))
  have p0058 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)))
  have p0059 :=
    @g_n_3eqtr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (syn_cima (syn_clec) (syn_csn C))))) (syn_cwppreach F C) (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) p0056 p0057 p0058
  have p0060 :=
    @g_ineq12d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C) (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) p0033 p0059
  have p0061 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand F C)))
  have p0062 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)))
  have p0063 :=
    @g_n_3eqtr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C)) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)) (syn_cwppcand F C) (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) p0060 p0061 p0062
  have p0064 :=
    @g_raleqdv (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_wbr (.cv n) (syn_clec) (.cv z)) z (syn_cwppcand F C) (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) dv_cache_0008 dv_cache_0009 p0063
  have p0065 :=
    @g_rexeqbidv (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))) (syn_wral z (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) (syn_wbr (.cv n) (syn_clec) (.cv z))) n (syn_cwppcand F C) (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0032 p0064
  have p0066 :=
    @g_imbi12d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) (syn_wrex n (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) (syn_wral z (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) p0001 p0065
  have p0067 :=
    @g_tru
  have p0068 :=
    @g_simpr syn_wtru (.classMem F (syn_cvv))
  have p0069 :=
    @g_n_0ex
  have p0070 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv)) (syn_wa syn_wtru (.neg (.classMem F (syn_cvv)))) p0069
  have p0071 :=
    @g_ifclda syn_wtru (.classMem F (syn_cvv)) F (syn_c0) (syn_cvv) p0068 p0070
  have p0072 :=
    Nominal.mp p0067 p0071
  have p0073 :=
    @g_wppcandminfixedpivotpairdrfdv z C D R n (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0072
  have p0074 :=
    @g_dedth (.classMem F (syn_cvv)) (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) (syn_wrex n (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) (syn_wral z (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) F (syn_c0) p0066 p0073
  exact p0074

noncomputable def g_wppcandminhwndv
    (z : Var) (C : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_n_z : n ≠ z) :
    Nominal.NPrf (.imp (syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ C.fv ∪ ({n} : Finset Var) ∪ F.fv
  let s : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_ne_z : s ≠ z := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_s : z ≠ s :=
    Ne.symm fresh_s_ne_z
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_ne_n : s ≠ n := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_s : n ≠ s :=
    Ne.symm fresh_s_ne_n
  have fresh_s_not_F : s ∉ F.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_ne_z : d ≠ z := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_d : z ≠ d :=
    Ne.symm fresh_d_ne_z
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_ne_n : d ≠ n := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_d : n ≠ d :=
    Ne.symm fresh_d_ne_n
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_ne_z : c ≠ z := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_c : z ≠ c :=
    Ne.symm fresh_c_ne_z
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_ne_n : c ≠ n := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_c : n ≠ c :=
    Ne.symm fresh_c_ne_n
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_s_ne_d : s ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_s : d ≠ s :=
    Ne.symm fresh_s_ne_d
  have fresh_s_ne_c : s ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_s : c ≠ s :=
    Ne.symm fresh_s_ne_c
  have fresh_d_ne_c : d ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_d : c ≠ d :=
    Ne.symm fresh_d_ne_c
  have dv_cache_0001 : s ∉ ((Wff.classEq (.cv c) C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_c, fresh_s_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : d ∉ ((Wff.classEq (.cv c) C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_c, fresh_d_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ≠ c := by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0004 : d ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0005 : c ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show c ≠ s from (by exact fresh_c_ne_s))
  have dv_cache_0006 : c ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : c ∉ ((syn_wb (.classMem C (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, fresh_c_ne_s, fresh_c_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : n ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show n ≠ z from (by exact dv_n_z))
  have dv_cache_0017 : d ∉ ((syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_C, fresh_d_not_F, fresh_d_ne_n, fresh_d_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : s ∉ ((syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_C, fresh_s_not_F, fresh_s_ne_n, fresh_s_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : d ∉ ((Wff.classMem F (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : s ∉ ((Wff.classMem F (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem C (syn_chwcards (syn_cvv)))
  have p0001 :=
    @g_elex C (syn_chwcards (syn_cvv))
  have p0002 :=
    @g_id (.classEq (.cv c) C)
  have p0003 :=
    @g_eleq1d (.classEq (.cv c) C) (.cv c) C (syn_chwcards (syn_cvv)) p0002
  have p0004 :=
    @g_id (.classEq (.cv c) C)
  have p0005 :=
    @g_eqeq1d (.classEq (.cv c) C) (.cv c) C (syn_cnc (.cv d)) p0004
  have p0006 :=
    @g_anbi2d (.classEq (.cv c) C) (.classEq (.cv c) (syn_cnc (.cv d))) (.classEq C (syn_cnc (.cv d))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) p0005
  have p0007 :=
    @g_exbidv (.classEq (.cv c) C) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))) s dv_cache_0001 p0006
  have p0008 :=
    @g_exbidv (.classEq (.cv c) C) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d))))) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d))))) d dv_cache_0002 p0007
  have p0009 :=
    @g_bibi12d (.classEq (.cv c) C) (.classMem (.cv c) (syn_chwcards (syn_cvv))) (.classMem C (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d)))))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))))) p0003 p0008
  have p0010 :=
    @g_elhwcardswev c s d dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0011 :=
    @g_vtoclg (syn_wb (.classMem (.cv c) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d))))))) (syn_wb (.classMem C (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d))))))) c C (syn_cvv) dv_cache_0006 dv_cache_0007 p0009 p0010
  have p0012 :=
    @g_syl (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cvv)) (syn_wb (.classMem C (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d))))))) p0001 p0011
  have p0013 :=
    @g_mpbid (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))))) p0000 p0012
  have p0014 :=
    @g_wppcandminfixedpivotsetdeddrfdv z C (.cv d) (.cv s) n F dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0015 :=
    @g_exlimdvv (.classMem F (syn_cvv)) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) d s dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0014
  have p0016 :=
    @g_syl5 (.classMem C (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))))) (.classMem F (syn_cvv)) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) p0013 p0015
  have p0017 :=
    @g_imp (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) p0016
  exact p0017

noncomputable def g_wppcandleastuniqclndv
    (A : Class) (B : Class) (C : Class) (k : Var) (F : Class) (dv_A_k : k ∉ A.fv) (dv_B_k : k ∉ B.fv) (dv_C_k : k ∉ C.fv) (dv_F_k : k ∉ F.fv) (hyp_wppcandleastuniqclndv_1 : Nominal.NPrf (.classMem A (syn_cwppcand F C))) (hyp_wppcandleastuniqclndv_2 : Nominal.NPrf (syn_wral k (syn_cwppcand F C) (syn_wbr A (syn_clec) (.cv k)))) (hyp_wppcandleastuniqclndv_3 : Nominal.NPrf (.classMem B (syn_cwppcand F C))) (hyp_wppcandleastuniqclndv_4 : Nominal.NPrf (syn_wral k (syn_cwppcand F C) (syn_wbr B (syn_clec) (.cv k)))) :
    Nominal.NPrf (.classEq A B) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ ({k} : Finset Var) ∪ F.fv
  have dv_cache_0001 : k ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : k ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((syn_wbr A (syn_clec) B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_k, dv_B_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : k ∉ ((syn_wbr B (syn_clec) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_k, dv_A_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv k) B)
  have p0001 :=
    @g_breq2d (.classEq (.cv k) B) (.cv k) B A (syn_clec) p0000
  have p0002 :=
    @g_rspcv (syn_wbr A (syn_clec) (.cv k)) (syn_wbr A (syn_clec) B) k B (syn_cwppcand F C) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    Nominal.mp hyp_wppcandleastuniqclndv_3 p0002
  have p0004 :=
    Nominal.mp hyp_wppcandleastuniqclndv_2 p0003
  have p0005 :=
    @g_id (.classEq (.cv k) A)
  have p0006 :=
    @g_breq2d (.classEq (.cv k) A) (.cv k) A B (syn_clec) p0005
  have p0007 :=
    @g_rspcv (syn_wbr B (syn_clec) (.cv k)) (syn_wbr B (syn_clec) A) k A (syn_cwppcand F C) dv_cache_0004 dv_cache_0002 dv_cache_0005 p0006
  have p0008 :=
    Nominal.mp hyp_wppcandleastuniqclndv_1 p0007
  have p0009 :=
    Nominal.mp hyp_wppcandleastuniqclndv_4 p0008
  have p0010 :=
    @g_pm3_2i (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) A) p0004 p0009
  have p0011 :=
    @g_elwppcand C A F
  have p0012 :=
    @g_biimpi (.classMem A (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) (.classMem A (syn_cwppreach F C))) p0011
  have p0013 :=
    Nominal.mp hyp_wppcandleastuniqclndv_1 p0012
  have p0014 :=
    @g_simpl (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) (.classMem A (syn_cwppreach F C))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_simpl (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_hwcardssnc (syn_cvv)
  have p0019 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) A p0018
  have p0020 :=
    Nominal.mp p0017 p0019
  have p0021 :=
    @g_elwppcand C B F
  have p0022 :=
    @g_biimpi (.classMem B (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem B (syn_chwcards (syn_cvv))) (syn_wbr B (syn_clec) C)) (.classMem B (syn_cwppreach F C))) p0021
  have p0023 :=
    Nominal.mp hyp_wppcandleastuniqclndv_3 p0022
  have p0024 :=
    @g_simpl (syn_wa (.classMem B (syn_chwcards (syn_cvv))) (syn_wbr B (syn_clec) C)) (.classMem B (syn_cwppreach F C))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_simpl (.classMem B (syn_chwcards (syn_cvv))) (syn_wbr B (syn_clec) C)
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_hwcardssnc (syn_cvv)
  have p0029 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) B p0028
  have p0030 :=
    Nominal.mp p0027 p0029
  have p0031 :=
    @g_pm3_2i (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) p0020 p0030
  have p0032 :=
    @g_sbth A B
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    Nominal.mp p0010 p0033
  exact p0034

#print axioms g_wppcandleastuniqclndv

end NFChoice.DirectNominalPrf.WPPReplay
