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
import NominalWPPReplayChunk014Compact001Part021

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

noncomputable def g_fdroweqmem
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)) (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let b : Var := freshVar proofSupport 0
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0014 : b ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0015 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0016 : b ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : b ∉ ((Wff.classMem C (syn_csep2 (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_C, fresh_b_ne_x, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show Disjoint ((Class.cv x)).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x), NFChoice.Compiler.CoreFVSimp.fv_class_cv (y)]; exact (show Disjoint (({x} : Finset Var)) (({y} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y))))))))
  have dv_cache_0019 : b ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : b ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : b ∉ ((syn_wb (.classMem C (syn_csep2 (.cv x) (.cv y))) (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_C, fresh_b_ne_x, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)
  have p0001 :=
    @g_fdroweqnosep x y A B R b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)) (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.neg (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) p0000 p0001
  have p0003 :=
    @g_simpr (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)
  have p0004 :=
    @g_eleq1 (.cv b) C (syn_csep2 (.cv x) (.cv y))
  have p0005 :=
    @g_rspcev (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))) (.classMem C (syn_csep2 (.cv x) (.cv y))) b C A dv_cache_0016 dv_cache_0003 dv_cache_0017 p0004
  have p0006 :=
    @g_ex (.classMem C A) (.classMem C (syn_csep2 (.cv x) (.cv y))) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) p0005
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)) (.classMem C A) (.imp (.classMem C (syn_csep2 (.cv x) (.cv y))) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))))) p0003 p0006
  have p0008 :=
    @g_mtod (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)) (.classMem C (syn_csep2 (.cv x) (.cv y))) (syn_wrex b A (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y)))) p0002 p0007
  have p0009 :=
    @g_simpr (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)
  have p0010 :=
    @g_elex C A
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)) (.classMem C A) (.classMem C (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_eleq1 (.cv b) C (syn_csep2 (.cv x) (.cv y))
  have p0013 :=
    @g_eleq2 (.cv b) C (.cv x)
  have p0014 :=
    @g_eleq2 (.cv b) C (.cv y)
  have p0015 :=
    @g_bibi12d (.classEq (.cv b) C) (.classMem (.cv x) (.cv b)) (.classMem (.cv x) C) (.classMem (.cv y) (.cv b)) (.classMem (.cv y) C) p0013 p0014
  have p0016 :=
    @g_notbid (.classEq (.cv b) C) (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))) (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C)) p0015
  have p0017 :=
    @g_bibi12d (.classEq (.cv b) C) (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))) (.classMem C (syn_csep2 (.cv x) (.cv y))) (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b)))) (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))) p0012 p0016
  have p0018 :=
    @g_sep2valJp (.cv x) (.cv y) b dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0019 :=
    @g_xor (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))
  have p0020 :=
    @g_bicomi (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b)))) (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b)))) (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b))))) p0019
  have p0021 :=
    @g_bitri (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))) (syn_wo (syn_wa (.classMem (.cv x) (.cv b)) (.neg (.classMem (.cv y) (.cv b)))) (syn_wa (.classMem (.cv y) (.cv b)) (.neg (.classMem (.cv x) (.cv b))))) (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b)))) p0018 p0020
  have p0022 :=
    @g_vtoclg (syn_wb (.classMem (.cv b) (syn_csep2 (.cv x) (.cv y))) (.neg (syn_wb (.classMem (.cv x) (.cv b)) (.classMem (.cv y) (.cv b))))) (syn_wb (.classMem C (syn_csep2 (.cv x) (.cv y))) (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C)))) b C (syn_cvv) dv_cache_0016 dv_cache_0021 p0017 p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)) (.classMem C (syn_cvv)) (syn_wb (.classMem C (syn_csep2 (.cv x) (.cv y))) (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C)))) p0011 p0022
  have p0024 :=
    @g_notbid (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)) (.classMem C (syn_csep2 (.cv x) (.cv y))) (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C))) p0023
  have p0025 :=
    @g_mpbid (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)) (.neg (.classMem C (syn_csep2 (.cv x) (.cv y)))) (.neg (.neg (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C)))) p0008 p0024
  have p0026 :=
    @g_notnotrd (syn_wa (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem C A)) (syn_wb (.classMem (.cv x) C) (.classMem (.cv y) C)) p0025
  exact p0026

noncomputable def g_fdrowrelex2
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdrowrelex2_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdrowrelex2_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdrowrelex2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrowrel R A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have p0000 :=
    (by simpa [syn_cfdrowrel] using (Nominal.classEqRefl (syn_cfdrowrel R A B)))
  have p0001 :=
    @g_a1i (.classEq (syn_cfdrowrel R A B) (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B)))) (syn_wbr R (syn_cwe) A) p0000
  have p0002 :=
    @g_fdmemex
  have p0003 :=
    @g_kqrelex (syn_cfdmem) p0002
  have p0004 :=
    @g_a1i (.classMem (syn_ckqrel (syn_cfdmem)) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0003
  have p0005 :=
    @g_fdifex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdrowrelex2_1 hyp_fdrowrelex2_2 hyp_fdrowrelex2_3
  have p0006 :=
    @g_pw1exg (syn_cfdif R A B) (syn_cvv)
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdif R A B) (syn_cvv)) (.classMem (syn_cpw1 (syn_cfdif R A B)) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_ckqrel (syn_cfdmem)) (syn_cvv)) (.classMem (syn_cpw1 (syn_cfdif R A B)) (syn_cvv)) p0004 p0007
  have p0009 :=
    @g_resexg (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B)) (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (syn_ckqrel (syn_cfdmem)) (syn_cvv)) (.classMem (syn_cpw1 (syn_cfdif R A B)) (syn_cvv))) (.classMem (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B))) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A) (syn_cfdrowrel R A B) (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B))) (syn_cvv) p0001 p0010
  exact p0011

noncomputable def g_elfdrowfibg
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf (.imp (.classMem D (syn_cvv)) (syn_wb (.classMem D (syn_cfdrowfib R A B C)) (.classMem (syn_cop (syn_csn D) C) (syn_cfdrowrel R A B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0009 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : d ∉ ((Wff.classMem (syn_cop (syn_csn D) C) (syn_cfdrowrel R A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_D, fresh_d_not_C, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv d) D)
  have p0001 :=
    @g_sneqd (.classEq (.cv d) D) (.cv d) D p0000
  have p0002 :=
    @g_opeq1d (.classEq (.cv d) D) (syn_csn (.cv d)) (syn_csn D) C p0001
  have p0003 :=
    @g_eleq1d (.classEq (.cv d) D) (syn_cop (syn_csn (.cv d)) C) (syn_cop (syn_csn D) C) (syn_cfdrowrel R A B) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrowfib A B C R d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0005 :=
    @g_elab2g (.classMem (syn_cop (syn_csn (.cv d)) C) (syn_cfdrowrel R A B)) (.classMem (syn_cop (syn_csn D) C) (syn_cfdrowrel R A B)) d D (syn_cfdrowfib R A B C) (syn_cvv) dv_cache_0011 dv_cache_0012 p0003 p0004
  exact p0005

noncomputable def g_fdrowfibeq4
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf (.imp (.classEq C D) (.classEq (syn_cfdrowfib R A B C) (syn_cfdrowfib R A B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : d ∉ ((Wff.classEq C D)).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_C, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint (A).fv (B).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0003 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0004 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0007 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0010 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : Disjoint (A).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0013 : Disjoint (B).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0014 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0015 : d ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq C D)
  have p0001 :=
    @g_opeq2d (.classEq C D) C D (syn_csn (.cv d)) p0000
  have p0002 :=
    @g_eleq1d (.classEq C D) (syn_cop (syn_csn (.cv d)) C) (syn_cop (syn_csn (.cv d)) D) (syn_cfdrowrel R A B) p0001
  have p0003 :=
    @g_abbidv (.classEq C D) (.classMem (syn_cop (syn_csn (.cv d)) C) (syn_cfdrowrel R A B)) (.classMem (syn_cop (syn_csn (.cv d)) D) (syn_cfdrowrel R A B)) d dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrowfib A B C R d dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrowfib A B D R d dv_cache_0002 dv_cache_0012 dv_cache_0004 dv_cache_0005 dv_cache_0013 dv_cache_0007 dv_cache_0008 dv_cache_0014 dv_cache_0015 dv_cache_0011
  have p0006 :=
    @g_n_3eqtr4g (.classEq C D) (.cab d (.classMem (syn_cop (syn_csn (.cv d)) C) (syn_cfdrowrel R A B))) (.cab d (.classMem (syn_cop (syn_csn (.cv d)) D) (syn_cfdrowrel R A B))) (syn_cfdrowfib R A B C) (syn_cfdrowfib R A B D) p0003 p0004 p0005
  exact p0006

noncomputable def g_fdrowfibsn2
    (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) (hyp_fdrowfibsn2_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfdrowfib R A B (syn_csn (syn_csn C))) (syn_cfdrow R A B C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((syn_csn (syn_csn C))).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv ((syn_csn (syn_csn C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((A).fv) (((syn_csn C)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (A).fv (C).fv from (by exact dv_A_C))))))
  have dv_cache_0003 : Disjoint (A).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (A).fv from (by exact fresh_d_not_A))))))
  have dv_cache_0004 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : Disjoint (B).fv ((syn_csn (syn_csn C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv ((syn_csn (syn_csn C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((B).fv) (((syn_csn C)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (B).fv (C).fv from (by exact dv_B_C))))))
  have dv_cache_0006 : Disjoint (B).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (B).fv from (by exact fresh_d_not_B))))))
  have dv_cache_0007 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : Disjoint ((syn_csn (syn_csn C))).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint ((syn_csn (syn_csn C))).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (((syn_csn C)).fv) (({d} : Finset Var)) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((C).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (C).fv from (by exact fresh_d_not_C))))))))
  have dv_cache_0009 : Disjoint ((syn_csn (syn_csn C))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint ((syn_csn (syn_csn C))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (((syn_csn C)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (C).fv (R).fv from (by exact dv_C_R))))))
  have dv_cache_0010 : Disjoint ((Class.cv d)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint ((Class.cv d)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({d} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show d ∉ (R).fv from (by exact fresh_d_not_R))))))
  have dv_cache_0011 : Disjoint ((syn_cfdmem)).fv ((syn_csn (.cv d))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint ((syn_cfdmem)).fv ((syn_csn (.cv d))).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((∅ : Finset Var)) (((Class.cv d)).fv) from (by simp))))
  have dv_cache_0012 : Disjoint ((syn_cfdmem)).fv ((syn_csn (syn_csn C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint ((syn_cfdmem)).fv ((syn_csn (syn_csn C))).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((∅ : Finset Var)) (((syn_csn C)).fv) from (by simp))))
  have dv_cache_0013 : Disjoint ((syn_csn (.cv d))).fv ((syn_csn (syn_csn C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show Disjoint ((syn_csn (.cv d))).fv ((syn_csn (syn_csn C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn ((Class.cv d)), NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn ((syn_csn C))]; exact (show Disjoint (((Class.cv d)).fv) (((syn_csn C)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({d} : Finset Var)) (((syn_csn C)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (({d} : Finset Var)) ((C).fv) from (Finset.disjoint_singleton_left.mpr (show d ∉ (C).fv from (by exact fresh_d_not_C))))))))))
  have dv_cache_0014 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0016 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0017 : Disjoint (C).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show Disjoint (C).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((C).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (C).fv from (by exact fresh_d_not_C))))))
  have dv_cache_0018 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0019 : d ∉ ((syn_cfdrowfib R A B (syn_csn (syn_csn C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_not_C, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : d ∉ ((syn_cfdrow R A B C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_not_C, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex d
  have p0001 :=
    @g_elfdrowfibg A B (syn_csn (syn_csn C)) (.cv d) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    (by simpa [syn_cfdrowrel] using (Nominal.classEqRefl (syn_cfdrowrel R A B)))
  have p0004 :=
    @g_eleq2i (syn_cfdrowrel R A B) (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B))) (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) p0003
  have p0005 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C)))) (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdrowrel R A B)) (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B)))) p0002 p0004
  have p0006 :=
    @g_opelres (syn_csn (.cv d)) (syn_csn (syn_csn C)) (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B))
  have p0007 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C)))) (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cres (syn_ckqrel (syn_cfdmem)) (syn_cpw1 (syn_cfdif R A B)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_ckqrel (syn_cfdmem))) (.classMem (syn_csn (.cv d)) (syn_cpw1 (syn_cfdif R A B)))) p0005 p0006
  have p0008 :=
    @g_snex (.cv d)
  have p0009 :=
    @g_snex (syn_csn C)
  have p0010 :=
    @g_kqrelbr (syn_cfdmem) (syn_csn (.cv d)) (syn_csn (syn_csn C)) dv_cache_0011 dv_cache_0012 dv_cache_0013 p0008 p0009
  have p0011 :=
    @g_snelpw1 (.cv d) (syn_cfdif R A B)
  have p0012 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_ckqrel (syn_cfdmem))) (.classMem (syn_copk (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem (syn_csn (.cv d)) (syn_cpw1 (syn_cfdif R A B))) (.classMem (.cv d) (syn_cfdif R A B)) p0010 p0011
  have p0013 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_ckqrel (syn_cfdmem))) (.classMem (syn_csn (.cv d)) (syn_cpw1 (syn_cfdif R A B)))) (syn_wa (.classMem (syn_copk (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem (.cv d) (syn_cfdif R A B))) p0007 p0012
  have p0014 :=
    @g_fdmemval C d dv_cache_0014 hyp_fdrowfibsn2_1
  have p0015 :=
    @g_anbi1i (.classMem (syn_copk (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem C (.cv d)) (.classMem (.cv d) (syn_cfdif R A B)) p0014
  have p0016 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C)))) (syn_wa (.classMem (syn_copk (syn_csn (.cv d)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem (.cv d) (syn_cfdif R A B))) (syn_wa (.classMem C (.cv d)) (.classMem (.cv d) (syn_cfdif R A B))) p0013 p0015
  have p0017 :=
    @g_ancom (.classMem C (.cv d)) (.classMem (.cv d) (syn_cfdif R A B))
  have p0018 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C)))) (syn_wa (.classMem C (.cv d)) (.classMem (.cv d) (syn_cfdif R A B))) (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d))) p0016 p0017
  have p0019 :=
    @g_elfdrowg A B C (.cv d) R dv_cache_0001 dv_cache_0015 dv_cache_0003 dv_cache_0004 dv_cache_0016 dv_cache_0006 dv_cache_0007 dv_cache_0017 dv_cache_0018 dv_cache_0010
  have p0020 :=
    @g_bicomi (.classMem (.cv d) (syn_cfdrow R A B C)) (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d))) p0019
  have p0021 :=
    @g_bitri (.classMem (.cv d) (syn_cfdrowfib R A B (syn_csn (syn_csn C)))) (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d))) (.classMem (.cv d) (syn_cfdrow R A B C)) p0018 p0020
  have p0022 :=
    @g_eqriv d (syn_cfdrowfib R A B (syn_csn (syn_csn C))) (syn_cfdrow R A B C) dv_cache_0019 dv_cache_0020 p0021
  exact p0022

#print axioms g_fdrowfibsn2

end NFChoice.DirectNominalPrf.WPPReplay
