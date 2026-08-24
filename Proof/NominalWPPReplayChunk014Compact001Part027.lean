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
import NominalWPPReplayChunk014Compact001Part026

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

noncomputable def g_fdpointimage
    (A : Class) (c : Var) (dv_A_c : c ∉ A.fv) (hyp_fdpointimage_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv c) A) (.classEq (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c)))) (syn_cpw1 (syn_cpw1 (.cv c))))) := by
  let proofSupport : Finset Var := A.fv ∪ ({c} : Finset Var)
  let d : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_ne_c : d ≠ c := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_d : c ≠ d :=
    Ne.symm fresh_d_ne_c
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_c : y ≠ c := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_y : c ≠ y :=
    Ne.symm fresh_y_ne_c
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_c : x ≠ c := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_x : c ≠ x :=
    Ne.symm fresh_x_ne_c
  have fresh_d_ne_y : d ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_d : y ≠ d :=
    Ne.symm fresh_d_ne_y
  have fresh_d_ne_x : d ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : Disjoint ((syn_cfdmem)).fv ((syn_csn (.cv c))).fv := by
    exact (show Disjoint ((syn_cfdmem)).fv ((syn_csn (.cv c))).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint ((∅ : Finset Var)) (((Class.cv c)).fv) from (by simp))))
  have dv_cache_0002 : Disjoint ((syn_cfdmem)).fv ((Class.cv d)).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((syn_cfdmem)).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((∅ : Finset Var)) (({d} : Finset Var)) from (by simp))))
  have dv_cache_0003 : Disjoint ((syn_csn (.cv c))).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint ((syn_csn (.cv c))).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (((Class.cv c)).fv) (({d} : Finset Var)) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({c} : Finset Var)) (({d} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show c ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ d from (by exact fresh_c_ne_d))))))))))
  have dv_cache_0004 : x ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cuni A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : c ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq (.cv d) (syn_csn (syn_csn (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_d, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_d, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Wff.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : c ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((Wff.classEq (.cv d) (syn_csn (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_d, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_c, fresh_y_ne_d, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Wff.classMem (.cv c) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_c, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : d ∉ ((syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, fresh_d_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : d ∉ ((syn_cpw1 (syn_cpw1 (.cv c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : d ∉ ((Wff.classMem (.cv c) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_c, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elimasn (syn_cfdpointrel A) (syn_csn (.cv c)) (.cv d)
  have p0001 :=
    (by simpa [syn_cfdpointrel] using (Nominal.classEqRefl (syn_cfdpointrel A)))
  have p0002 :=
    @g_eleq2i (syn_cfdpointrel A) (syn_cin (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))) (syn_cop (syn_csn (.cv c)) (.cv d)) p0001
  have p0003 :=
    @g_bitri (.classMem (.cv d) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c))))) (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cfdpointrel A)) (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cin (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))) p0000 p0002
  have p0004 :=
    @g_elin (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
  have p0005 :=
    @g_snex (.cv c)
  have p0006 :=
    @g_vex d
  have p0007 :=
    @g_kqrelbr (syn_cfdmem) (syn_csn (.cv c)) (.cv d) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0005 p0006
  have p0008 :=
    @g_snex (.cv c)
  have p0009 :=
    @g_opelxp (syn_csn (.cv c)) (.cv d) (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))
  have p0010 :=
    @g_mpbiran (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))) (.classMem (syn_csn (.cv c)) (syn_cvv)) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) p0008 p0009
  have p0011 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_ckqrel (syn_cfdmem))) (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) p0007 p0010
  have p0012 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cin (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_ckqrel (syn_cfdmem))) (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A))))) p0004 p0011
  have p0013 :=
    @g_bitri (.classMem (.cv d) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c))))) (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cin (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A))))) p0003 p0012
  have p0014 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c))))) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))) (.classMem (.cv c) A) p0013
  have p0015 :=
    @g_elpw12 x (.cv d) (syn_cuni A) dv_cache_0004 dv_cache_0005
  have p0016 :=
    @g_a1i (syn_wb (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))) (.classMem (.cv c) A) p0015
  have p0017 :=
    @g_anbi2d (.classMem (.cv c) A) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) p0016
  have p0018 :=
    @g_simpl (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
  have p0019 :=
    @g_simpr (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
  have p0020 :=
    @g_id (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
  have p0021 :=
    @g_opkeq2d (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) (.cv d) (syn_csn (syn_csn (.cv x))) (syn_csn (.cv c)) p0020
  have p0022 :=
    @g_eleq1d (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv x)))) (syn_cfdmem) p0021
  have p0023 :=
    @g_vex x
  have p0024 :=
    @g_fdmemval (.cv x) c dv_cache_0006 p0023
  have p0025 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv x)))) (syn_cfdmem)) (.classMem (.cv x) (.cv c))) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) p0024
  have p0026 :=
    @g_bitrd (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv x)))) (syn_cfdmem)) (.classMem (.cv x) (.cv c)) p0022 p0025
  have p0027 :=
    @g_syl (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) (syn_wb (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (.cv x) (.cv c))) p0019 p0026
  have p0028 :=
    @g_mpbid (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (.cv x) (.cv c)) p0018 p0027
  have p0029 :=
    @g_simpr (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
  have p0030 :=
    @g_jca (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) (.classMem (.cv x) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) p0028 p0029
  have p0031 :=
    @g_id (.classEq (.cv y) (.cv x))
  have p0032 :=
    @g_sneqd (.classEq (.cv y) (.cv x)) (.cv y) (.cv x) p0031
  have p0033 :=
    @g_sneqd (.classEq (.cv y) (.cv x)) (syn_csn (.cv y)) (syn_csn (.cv x)) p0032
  have p0034 :=
    @g_eqeq2d (.classEq (.cv y) (.cv x)) (syn_csn (syn_csn (.cv y))) (syn_csn (syn_csn (.cv x))) (.cv d) p0033
  have p0035 :=
    @g_rspcev (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) y (.cv x) (.cv c) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0034
  have p0036 :=
    @g_syl (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) (syn_wa (.classMem (.cv x) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0030 p0035
  have p0037 :=
    @g_ex (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0036
  have p0038 :=
    @g_a1d (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.imp (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))) (.classMem (.cv x) (syn_cuni A)) p0037
  have p0039 :=
    @g_rexlimdv (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) x (syn_cuni A) dv_cache_0010 dv_cache_0011 p0038
  have p0040 :=
    @g_imp (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0039
  have p0041 :=
    @g_a1i (.imp (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))) (.classMem (.cv c) A) p0040
  have p0042 :=
    @g_simprl (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
  have p0043 :=
    @g_simprr (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
  have p0044 :=
    @g_id (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
  have p0045 :=
    @g_opkeq2d (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) (.cv d) (syn_csn (syn_csn (.cv y))) (syn_csn (.cv c)) p0044
  have p0046 :=
    @g_eleq1d (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv y)))) (syn_cfdmem) p0045
  have p0047 :=
    @g_vex y
  have p0048 :=
    @g_fdmemval (.cv y) c dv_cache_0012 p0047
  have p0049 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv y)))) (syn_cfdmem)) (.classMem (.cv y) (.cv c))) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) p0048
  have p0050 :=
    @g_bitrd (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv y)))) (syn_cfdmem)) (.classMem (.cv y) (.cv c)) p0046 p0049
  have p0051 :=
    @g_biimprd (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (.cv y) (.cv c)) p0050
  have p0052 :=
    @g_syl (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) (.imp (.classMem (.cv y) (.cv c)) (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))) p0043 p0051
  have p0053 :=
    @g_mpd (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))) (.classMem (.cv y) (.cv c)) (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) p0042 p0052
  have p0054 :=
    @g_simpl (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))
  have p0055 :=
    @g_simprl (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
  have p0056 :=
    @g_jca (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))) (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)) p0054 p0055
  have p0057 :=
    @g_elssuni (.cv c) A
  have p0058 :=
    @g_sselda (.classMem (.cv c) A) (.cv c) (syn_cuni A) (.cv y) p0057
  have p0059 :=
    @g_syl (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv c) A) (.classMem (.cv y) (.cv c))) (.classMem (.cv y) (syn_cuni A)) p0056 p0058
  have p0060 :=
    @g_simprr (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
  have p0061 :=
    @g_jca (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))) (.classMem (.cv y) (syn_cuni A)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) p0059 p0060
  have p0062 :=
    @g_id (.classEq (.cv x) (.cv y))
  have p0063 :=
    @g_sneqd (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) p0062
  have p0064 :=
    @g_sneqd (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y)) p0063
  have p0065 :=
    @g_eqeq2d (.classEq (.cv x) (.cv y)) (syn_csn (syn_csn (.cv x))) (syn_csn (syn_csn (.cv y))) (.cv d) p0064
  have p0066 :=
    @g_rspcev (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) x (.cv y) (syn_cuni A) dv_cache_0013 dv_cache_0005 dv_cache_0014 p0065
  have p0067 :=
    @g_syl (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))) (syn_wa (.classMem (.cv y) (syn_cuni A)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) p0061 p0066
  have p0068 :=
    @g_jca (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))) (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) p0053 p0067
  have p0069 :=
    @g_ex (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))) p0068
  have p0070 :=
    @g_exp3a (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))) p0069
  have p0071 :=
    @g_rexlimdv (.classMem (.cv c) A) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))) y (.cv c) dv_cache_0015 dv_cache_0016 p0070
  have p0072 :=
    @g_impbid (.classMem (.cv c) A) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0041 p0071
  have p0073 :=
    @g_bitrd (.classMem (.cv c) A) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A))))) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0017 p0072
  have p0074 :=
    @g_elpw12 y (.cv d) (.cv c) dv_cache_0017 dv_cache_0008
  have p0075 :=
    @g_bicomi (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (.cv c)))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0074
  have p0076 :=
    @g_a1i (syn_wb (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (.cv c))))) (.classMem (.cv c) A) p0075
  have p0077 :=
    @g_bitrd (.classMem (.cv c) A) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A))))) (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (.cv c)))) p0073 p0076
  have p0078 :=
    @g_bitrd (.classMem (.cv c) A) (.classMem (.cv d) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c))))) (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A))))) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (.cv c)))) p0014 p0077
  have p0079 :=
    @g_eqrdv (.classMem (.cv c) A) d (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c)))) (syn_cpw1 (syn_cpw1 (.cv c))) dv_cache_0018 dv_cache_0019 dv_cache_0020 p0078
  exact p0079

noncomputable def g_fdglobalrowima
    (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (.classEq (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 C))) (syn_cfdcode R A B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((syn_cpw1 (syn_cpw1 C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0010 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0011 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0012 : u ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (.classMem C A)
  have p0001 :=
    @g_fdglobalrowval u A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_wbr R (syn_cwe) A) (.classEq (syn_cfdglobalrowmap R A B) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))) p0000 p0001
  have p0003 :=
    @g_imaeq1d (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_cfdglobalrowmap R A B) (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C)) p0002
  have p0004 :=
    @g_dfima3 (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C))
  have p0005 :=
    @g_a1i (.classEq (syn_cima (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C))) (syn_crn (syn_cres (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C))))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) p0004
  have p0006 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 C))) (syn_cima (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C))) (syn_crn (syn_cres (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C)))) p0003 p0005
  have p0007 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (.classMem C A)
  have p0008 :=
    @g_elssuni C A
  have p0009 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (.classMem C A) (syn_wss C (syn_cuni A)) p0007 p0008
  have p0010 :=
    @g_pw1ss C (syn_cuni A)
  have p0011 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_wss C (syn_cuni A)) (syn_wss (syn_cpw1 C) (syn_cpw1 (syn_cuni A))) p0009 p0010
  have p0012 :=
    @g_pw1ss (syn_cpw1 C) (syn_cpw1 (syn_cuni A))
  have p0013 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_wss (syn_cpw1 C) (syn_cpw1 (syn_cuni A))) (syn_wss (syn_cpw1 (syn_cpw1 C)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) p0011 p0012
  have p0014 :=
    @g_resmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u)) dv_cache_0007 dv_cache_0008
  have p0015 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_wss (syn_cpw1 (syn_cpw1 C)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (.classEq (syn_cres (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C))) (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u)))) p0013 p0014
  have p0016 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdcodemap2 u A B C R dv_cache_0001 dv_cache_0009 dv_cache_0002 dv_cache_0003 dv_cache_0010 dv_cache_0004 dv_cache_0005 dv_cache_0011 dv_cache_0012 dv_cache_0006
  have p0017 :=
    @g_eqcomi (syn_cfdcodemap2 R A B C) (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))) p0016
  have p0018 :=
    @g_a1i (.classEq (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))) (syn_cfdcodemap2 R A B C)) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) p0017
  have p0019 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_cres (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C))) (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))) (syn_cfdcodemap2 R A B C) p0015 p0018
  have p0020 :=
    @g_rneqd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_cres (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C))) (syn_cfdcodemap2 R A B C) p0019
  have p0021 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 C))) (syn_crn (syn_cres (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_cpw1 (syn_cpw1 C)))) (syn_crn (syn_cfdcodemap2 R A B C)) p0006 p0020
  have p0022 :=
    @g_fdcodeeqrnmap2 A B C R dv_cache_0001 dv_cache_0009 dv_cache_0002 dv_cache_0010 dv_cache_0004 dv_cache_0011
  have p0023 :=
    @g_eqcomi (syn_cfdcode R A B C) (syn_crn (syn_cfdcodemap2 R A B C)) p0022
  have p0024 :=
    @g_a1i (.classEq (syn_crn (syn_cfdcodemap2 R A B C)) (syn_cfdcode R A B C)) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) p0023
  have p0025 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 C))) (syn_crn (syn_cfdcodemap2 R A B C)) (syn_cfdcode R A B C) p0021 p0024
  exact p0025

noncomputable def g_fdcolcodemapex
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdcolcodemapex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcolcodemapex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcolcodemapex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcolcodemap R A B) (syn_cvv))) := by
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
    (by simpa [syn_cfdcolcodemap] using (Nominal.classEqRefl (syn_cfdcolcodemap R A B)))
  have p0001 :=
    @g_fdglobalrowex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapex_1 hyp_fdcolcodemapex_2 hyp_fdcolcodemapex_3
  have p0002 :=
    @g_imageex (syn_cfdglobalrowmap R A B) p0001
  have p0003 :=
    @g_fdpointrelex A hyp_fdcolcodemapex_2
  have p0004 :=
    @g_imageex (syn_cfdpointrel A) p0003
  have p0005 :=
    @g_coex (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)) p0002 p0004
  have p0006 :=
    @g_pw1ex A hyp_fdcolcodemapex_2
  have p0007 :=
    @g_pw1ex (syn_cpw1 A) p0006
  have p0008 :=
    @g_resex (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A)) p0005 p0007
  have p0009 :=
    @g_eqeltri (syn_cfdcolcodemap R A B) (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (syn_cvv) p0000 p0008
  have p0010 :=
    @g_a1i (.classMem (syn_cfdcolcodemap R A B) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0009
  exact p0010

noncomputable def g_fdcolcodemapfn
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdcolcodemapfn_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdcolcodemapfn_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdcolcodemapfn_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0004 : x ∉ ((syn_crn (syn_cimage (syn_cfdpointrel A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cpw1 (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdglobalrowex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapfn_1 hyp_fdcolcodemapfn_2 hyp_fdcolcodemapfn_3
  have p0001 :=
    @g_wppimagefn (syn_cfdglobalrowmap R A B) p0000
  have p0002 :=
    @g_fdpointrelex A hyp_fdcolcodemapfn_2
  have p0003 :=
    @g_wppimagefn (syn_cfdpointrel A) p0002
  have p0004 :=
    @g_elex (.cv x) (syn_crn (syn_cimage (syn_cfdpointrel A)))
  have p0005 :=
    @g_ssriv x (syn_crn (syn_cimage (syn_cfdpointrel A))) (syn_cvv) dv_cache_0004 dv_cache_0005 p0004
  have p0006 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))
  have p0007 :=
    @g_mp3an (syn_wfn (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cvv)) (syn_wfn (syn_cimage (syn_cfdpointrel A)) (syn_cvv)) (syn_wss (syn_crn (syn_cimage (syn_cfdpointrel A))) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cvv)) p0001 p0003 p0005 p0006
  have p0008 :=
    @g_fnresin1 (syn_cvv) (syn_cpw1 (syn_cpw1 A)) (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_elex (.cv x) (syn_cpw1 (syn_cpw1 A))
  have p0011 :=
    @g_ssriv x (syn_cpw1 (syn_cpw1 A)) (syn_cvv) dv_cache_0006 dv_cache_0005 p0010
  have p0012 :=
    @g_sseqin2 (syn_cpw1 (syn_cpw1 A)) (syn_cvv)
  have p0013 :=
    @g_mpbi (syn_wss (syn_cpw1 (syn_cpw1 A)) (syn_cvv)) (.classEq (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A))) p0011 p0012
  have p0014 :=
    @g_reseq2i (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A)) (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) p0013
  have p0015 :=
    @g_fneq1i (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))) (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A)))) (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) p0014
  have p0016 :=
    @g_mpbi (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A)))) (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A)))) (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A)))) p0009 p0015
  have p0017 :=
    @g_elex (.cv x) (syn_cpw1 (syn_cpw1 A))
  have p0018 :=
    @g_ssriv x (syn_cpw1 (syn_cpw1 A)) (syn_cvv) dv_cache_0006 dv_cache_0005 p0017
  have p0019 :=
    @g_sseqin2 (syn_cpw1 (syn_cpw1 A)) (syn_cvv)
  have p0020 :=
    @g_mpbi (syn_wss (syn_cpw1 (syn_cpw1 A)) (syn_cvv)) (.classEq (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A))) p0018 p0019
  have p0021 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A)) (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) p0020
  have p0022 :=
    @g_mpbi (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A)))) (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A))) p0016 p0021
  have p0023 :=
    (by simpa [syn_cfdcolcodemap] using (Nominal.classEqRefl (syn_cfdcolcodemap R A B)))
  have p0024 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 A)) (syn_cfdcolcodemap R A B) (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) p0023
  have p0025 :=
    @g_mpbir (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))) (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A))) p0022 p0024
  have p0026 :=
    @g_a1i (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))) (syn_wbr R (syn_cwe) A) p0025
  exact p0026

#print axioms g_fdcolcodemapfn

end NFChoice.DirectNominalPrf.WPPReplay
