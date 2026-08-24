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
import NominalWPPReplayChunk014Compact001Part020

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

noncomputable def g_fpivex
    (x : Var) (y : Var) (A : Class) (R : Class) (b : Var) (d : Var) (dv_A_R : Disjoint A.fv R.fv) (dv_A_b : b ∉ A.fv) (dv_A_d : d ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_R_b : b ∉ R.fv) (dv_R_d : d ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_b_d : b ≠ d) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_d_x : d ≠ x) (dv_d_y : d ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_wrex d A (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ R.fv ∪ ({b} : Finset Var) ∪ ({d} : Finset Var)
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have fresh_c_ne_y : c ≠ y := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_c : y ≠ c :=
    Ne.symm fresh_c_ne_y
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_ne_b : c ≠ b := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_ne_c : b ≠ c :=
    Ne.symm fresh_c_ne_b
  have fresh_c_ne_d : c ≠ d := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_c : d ≠ c :=
    Ne.symm fresh_c_ne_d
  have dv_cache_0001 : b ∉ ((syn_csep2 (.cv x) (.cv y))).fv := by
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_b_x, dv_b_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : c ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : c ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((Wff.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_b_d, dv_b_x, dv_b_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_d, dv_A_d, (Ne.symm dv_b_d), dv_d_x, dv_d_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : c ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, fresh_c_not_A, fresh_c_ne_b, fresh_c_ne_x, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((Wff.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_b_d), dv_d_x, dv_d_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : c ∉ ((Wff.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_x, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ ((Wff.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_c, dv_b_x, dv_b_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : b ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show b ≠ d from (by exact dv_b_d))
  have dv_cache_0015 : b ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0016 : d ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0017 : Disjoint (A).fv ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show Disjoint (A).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (A).fv from (by exact dv_A_x))))))
  have dv_cache_0018 : Disjoint (A).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show Disjoint (A).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (A).fv from (by exact dv_A_y))))))
  have dv_cache_0019 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0020 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show Disjoint ((Class.cv x)).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x), NFChoice.Compiler.CoreFVSimp.fv_class_cv (y)]; exact (show Disjoint (({x} : Finset Var)) (({y} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y))))))))
  have dv_cache_0021 : Disjoint ((Class.cv x)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact dv_R_x))))))
  have dv_cache_0022 : c ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : d ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : Disjoint ((Class.cv y)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show Disjoint ((Class.cv y)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show y ∉ (R).fv from (by exact dv_R_y))))))
  have dv_cache_0025 : c ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : d ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : c ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have p0000 :=
    @g_abid2 b (syn_csep2 (.cv x) (.cv y)) dv_cache_0001
  have p0001 :=
    @g_sep2ex2 x y dv_cache_0002
  have p0002 :=
    @g_eqeltri (.cab b (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) (syn_csep2 (.cv x) (.cv y)) (syn_cvv) p0000 p0001
  have p0003 :=
    @g_eleq1 (.cv b) (.cv d) (syn_csep2 (.cv x) (.cv y))
  have p0004 :=
    @g_eleq1 (.cv b) (.cv c) (syn_csep2 (.cv x) (.cv y))
  have p0005 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
  have p0006 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
  have p0007_e01_recanon : Nominal.NPrf (.imp (.objEq b d) (syn_wb (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csep2 syn_wo syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0007_e02_recanon : Nominal.NPrf (.imp (.objEq b c) (syn_wb (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))) (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csep2 syn_wo syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0007 :=
    @g_weds (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) b d c A R dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 p0002 p0007_e01_recanon p0007_e02_recanon p0005 p0006
  have p0008 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)
  have p0009 :=
    @g_a1d (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)) (.classMem (.cv d) A) (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) p0008
  have p0010 :=
    @g_simpl (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))
  have p0011 :=
    @g_a1i (.imp (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)) p0010
  have p0012 :=
    @g_jcad (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)) (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) p0009 p0011
  have p0013 :=
    @g_simpr (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))
  have p0014 :=
    @g_a1i (.imp (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)) p0013
  have p0015 :=
    @g_jcad (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)) (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))) p0012 p0014
  have p0016 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0005 dv_cache_0004 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0007 dv_cache_0006 dv_cache_0027
  have p0017 :=
    @g_biimpri (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) p0016
  have p0018 :=
    @g_syl6 (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)) (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) p0015 p0017
  have p0019 :=
    @g_reximdva (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c))))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) d A dv_cache_0009 p0018
  have p0020 :=
    @g_mpd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_wrex d A (syn_wa (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y))) (syn_wbr (.cv d) R (.cv c)))))) (syn_wrex d A (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) p0007 p0019
  exact p0020

noncomputable def g_fdrowdiff
    (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (b : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_b : b ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ ({b} : Finset Var)
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_ne_x : d ≠ x := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_d_ne_y : d ≠ y := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_d : y ≠ d :=
    Ne.symm fresh_d_ne_y
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_ne_b : d ≠ b := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_d : b ≠ d :=
    Ne.symm fresh_d_ne_b
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0002 : b ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : b ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show b ≠ d from (by exact fresh_b_ne_d))
  have dv_cache_0011 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show b ≠ x from (by exact dv_b_x))
  have dv_cache_0012 : b ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show b ≠ y from (by exact dv_b_y))
  have dv_cache_0013 : d ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0014 : d ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show d ≠ y from (by exact fresh_d_ne_y))
  have dv_cache_0015 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0016 : Disjoint (A).fv (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0017 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0018 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : d ∉ ((syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_ne_x, fresh_d_not_R, fresh_d_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : d ∉ ((syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_y, fresh_d_not_B, fresh_d_not_R, fresh_d_not_A, fresh_d_ne_x, fresh_d_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
  have p0001 :=
    @g_simp1 (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0002 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr R (syn_cwe) A) p0000 p0001
  have p0003 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
  have p0004 :=
    @g_jca (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) p0002 p0003
  have p0005 :=
    @g_fpivex x y A R b d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0006 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_wrex d A (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) p0004 p0005
  have p0007 :=
    @g_simpl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)
  have p0008 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) p0007 p0008
  have p0010 :=
    @g_fdrowsep x y A B R d dv_cache_0016 dv_cache_0001 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0011 :=
    @g_ex (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0010
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) A)) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.imp (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) p0009 p0011
  have p0013 :=
    @g_rexlimdva (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) d A dv_cache_0021 dv_cache_0022 p0012
  have p0014 :=
    @g_mpd (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) (syn_wrex d A (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0006 p0013
  exact p0014

noncomputable def g_fdroweqnosep
    (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (b : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_b : b ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_R_b : b ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.neg (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ ({b} : Finset Var)
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : b ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show b ≠ x from (by exact dv_b_x))
  have dv_cache_0014 : b ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show b ≠ y from (by exact dv_b_y))
  have dv_cache_0015 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_simpr (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0001 :=
    @g_nne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))
  have p0002 :=
    @g_bicomi (.neg (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0001
  have p0003 :=
    @g_sylib (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) (.neg (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) p0000 p0002
  have p0004 :=
    @g_simpl (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0005 :=
    @g_fdrowdiff x y A B R b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0006 :=
    @g_ex (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0005
  have p0007 :=
    @g_syl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.imp (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) p0004 p0006
  have p0008 :=
    @g_mtod (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) (syn_wne (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0003 p0007
  exact p0008

#print axioms g_fdroweqnosep

end NFChoice.DirectNominalPrf.WPPReplay
