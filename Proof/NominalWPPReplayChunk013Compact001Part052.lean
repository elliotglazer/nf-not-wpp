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
import NominalWPPReplayChunk013Compact001Part051

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

noncomputable def g_dflec3
    (f : Var) (M : Class) (N : Class) (a : Var) (b : Var) (dv_M_a : a ∉ M.fv) (dv_N_a : a ∉ N.fv) (dv_N_b : b ∉ N.fv) (dv_a_b : a ≠ b) (dv_a_f : a ≠ f) (dv_b_f : b ≠ f) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wb (syn_wbr M (syn_clec) N) (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))) := by
  let proofSupport : Finset Var := ({f} : Finset Var) ∪ M.fv ∪ N.fv ∪ ({a} : Finset Var) ∪ ({b} : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_a : x ≠ a := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_a : y ≠ a := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_ne_f : c ≠ f := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_f_ne_c : f ≠ c :=
    Ne.symm fresh_c_ne_f
  have fresh_c_not_M : c ∉ M.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_N : c ∉ N.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_ne_a : c ≠ a := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_c : a ≠ c :=
    Ne.symm fresh_c_ne_a
  have fresh_c_ne_b : c ≠ b := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_c : b ≠ c :=
    Ne.symm fresh_c_ne_b
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_c : x ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_x : c ≠ x :=
    Ne.symm fresh_x_ne_c
  have fresh_y_ne_c : y ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_y : c ≠ y :=
    Ne.symm fresh_y_ne_c
  have dv_cache_0001 : x ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq M (syn_cnc (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq N (syn_cnc (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_N, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : c ∉ ((syn_cnc (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : c ∉ ((syn_cnc (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((syn_cnc (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : c ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show c ≠ b from (by exact fresh_c_ne_b))
  have dv_cache_0009 : b ∉ ((syn_cnc (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : f ∉ ((syn_cres (syn_cid) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : f ∉ ((syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_c, (Ne.symm dv_b_f), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : f ∉ ((Wff.objEq a c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_f), fresh_f_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_cnc (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_c, dv_a_b, dv_a_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : c ∉ ((syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_a, fresh_c_ne_b, fresh_c_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : c ∉ ((syn_crn (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : c ∉ ((syn_wss (syn_crn (.cv f)) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_f, fresh_c_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : f ∉ ((syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_c, (Ne.symm dv_b_f), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : f ∉ ((Wff.classMem (.cv a) (syn_cnc (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_f), fresh_f_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_c, dv_a_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : a ∉ ((syn_cnc (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : b ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show b ≠ a from (by exact Ne.symm dv_a_b))
  have dv_cache_0024 : b ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : a ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : a ∉ ((syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_a, fresh_a_ne_x, dv_N_a, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((syn_wb (syn_wbr M (syn_clec) N) (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, fresh_x_not_N, fresh_x_ne_a, fresh_x_ne_b, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((syn_wb (syn_wbr M (syn_clec) N) (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, fresh_y_not_N, fresh_y_ne_a, fresh_y_ne_b, fresh_y_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs x M dv_cache_0001
  have p0001 :=
    @g_elncs y N dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem M (syn_cncs)) (syn_wex x (.classEq M (syn_cnc (.cv x)))) (.classMem N (syn_cncs)) (syn_wex y (.classEq N (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y))) x y dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wa (syn_wex x (.classEq M (syn_cnc (.cv x)))) (syn_wex y (.classEq N (syn_cnc (.cv y))))) (syn_wex x (syn_wex y (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))))) p0002 p0003
  have p0005 :=
    @g_ncex (.cv x)
  have p0006 :=
    @g_ncex (.cv y)
  have p0007 :=
    @g_brlec c b (syn_cnc (.cv x)) (syn_cnc (.cv y)) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0005 p0006
  have p0008 :=
    @g_rexcom (syn_wss (.cv c) (.cv b)) c b (syn_cnc (.cv x)) (syn_cnc (.cv y)) dv_cache_0009 dv_cache_0006 dv_cache_0008
  have p0009 :=
    @g_f1oi (.cv c)
  have p0010 :=
    @g_f1of1 (.cv c) (.cv c) (syn_cres (syn_cid) (.cv c))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_f1ss (.cv c) (.cv c) (.cv b) (syn_cres (syn_cid) (.cv c))
  have p0013 :=
    @g_mpan (syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv c)) (syn_wss (.cv c) (.cv b)) (syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv b)) p0011 p0012
  have p0014 :=
    @g_idex
  have p0015 :=
    @g_vex c
  have p0016 :=
    @g_resex (syn_cid) (.cv c) p0014 p0015
  have p0017 :=
    @g_f1eq1 (.cv c) (.cv b) (.cv f) (syn_cres (syn_cid) (.cv c))
  have p0018 :=
    @g_spcev (syn_wf1 (.cv f) (.cv c) (.cv b)) (syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv b)) f (syn_cres (syn_cid) (.cv c)) dv_cache_0010 dv_cache_0011 p0016 p0017
  have p0019 :=
    @g_syl (syn_wss (.cv c) (.cv b)) (syn_wf1 (syn_cres (syn_cid) (.cv c)) (.cv c) (.cv b)) (syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b))) p0013 p0018
  have p0020 :=
    @g_f1eq2 (.cv a) (.cv c) (.cv b) (.cv f)
  have p0021_e00_recanon : Nominal.NPrf (.imp (.objEq a c) (syn_wb (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf1 (.cv f) (.cv c) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0020
  have p0021 :=
    @g_exbidv (.objEq a c) (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf1 (.cv f) (.cv c) (.cv b)) f dv_cache_0012 p0021_e00_recanon
  have p0022_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (.cv c)) (syn_wb (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))) (syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_ccnv syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0021
  have p0022 :=
    @g_rspcev (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))) (syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b))) a (.cv c) (syn_cnc (.cv x)) dv_cache_0013 dv_cache_0014 dv_cache_0015 p0022_e00_recanon
  have p0023 :=
    @g_sylan2 (syn_wss (.cv c) (.cv b)) (.classMem (.cv c) (syn_cnc (.cv x))) (syn_wex f (syn_wf1 (.cv f) (.cv c) (.cv b))) (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) p0019 p0022
  have p0024 :=
    @g_rexlimiva (syn_wss (.cv c) (.cv b)) (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) c (syn_cnc (.cv x)) dv_cache_0016 p0023
  have p0025 :=
    @g_vex a
  have p0026 :=
    @g_eqnc (.cv a) (.cv x) p0025
  have p0027 :=
    @g_elnc (.cv a) (.cv x)
  have p0028 :=
    @g_bitr4i (.classEq (syn_cnc (.cv a)) (syn_cnc (.cv x))) (syn_wbr (.cv a) (syn_cen) (.cv x)) (.classMem (.cv a) (syn_cnc (.cv x))) p0026 p0027
  have p0029 :=
    @g_f1f1orn (.cv a) (.cv b) (.cv f)
  have p0030 :=
    @g_vex f
  have p0031 :=
    @g_f1oen (.cv a) (syn_crn (.cv f)) (.cv f) p0030
  have p0032 :=
    @g_syl (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf1o (.cv f) (.cv a) (syn_crn (.cv f))) (syn_wbr (.cv a) (syn_cen) (syn_crn (.cv f))) p0029 p0031
  have p0033 :=
    @g_ensym (.cv a) (syn_crn (.cv f))
  have p0034 :=
    @g_sylib (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wbr (.cv a) (syn_cen) (syn_crn (.cv f))) (syn_wbr (syn_crn (.cv f)) (syn_cen) (.cv a)) p0032 p0033
  have p0035 :=
    @g_elnc (syn_crn (.cv f)) (.cv a)
  have p0036 :=
    @g_sylibr (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wbr (syn_crn (.cv f)) (syn_cen) (.cv a)) (.classMem (syn_crn (.cv f)) (syn_cnc (.cv a))) p0034 p0035
  have p0037 :=
    @g_eleq2 (syn_cnc (.cv a)) (syn_cnc (.cv x)) (syn_crn (.cv f))
  have p0038 :=
    @g_syl5ib (syn_wf1 (.cv f) (.cv a) (.cv b)) (.classMem (syn_crn (.cv f)) (syn_cnc (.cv a))) (.classEq (syn_cnc (.cv a)) (syn_cnc (.cv x))) (.classMem (syn_crn (.cv f)) (syn_cnc (.cv x))) p0036 p0037
  have p0039 :=
    @g_sylbir (.classMem (.cv a) (syn_cnc (.cv x))) (.classEq (syn_cnc (.cv a)) (syn_cnc (.cv x))) (.imp (syn_wf1 (.cv f) (.cv a) (.cv b)) (.classMem (syn_crn (.cv f)) (syn_cnc (.cv x)))) p0028 p0038
  have p0040 :=
    @g_imp (.classMem (.cv a) (syn_cnc (.cv x))) (syn_wf1 (.cv f) (.cv a) (.cv b)) (.classMem (syn_crn (.cv f)) (syn_cnc (.cv x))) p0039
  have p0041 :=
    @g_f1f (.cv a) (.cv b) (.cv f)
  have p0042 :=
    @g_frn (.cv a) (.cv b) (.cv f)
  have p0043 :=
    @g_syl (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf (.cv f) (.cv a) (.cv b)) (syn_wss (syn_crn (.cv f)) (.cv b)) p0041 p0042
  have p0044 :=
    @g_adantl (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wss (syn_crn (.cv f)) (.cv b)) (.classMem (.cv a) (syn_cnc (.cv x))) p0043
  have p0045 :=
    @g_sseq1 (.cv c) (syn_crn (.cv f)) (.cv b)
  have p0046 :=
    @g_rspcev (syn_wss (.cv c) (.cv b)) (syn_wss (syn_crn (.cv f)) (.cv b)) c (syn_crn (.cv f)) (syn_cnc (.cv x)) dv_cache_0017 dv_cache_0005 dv_cache_0018 p0045
  have p0047 :=
    @g_syl2anc (syn_wa (.classMem (.cv a) (syn_cnc (.cv x))) (syn_wf1 (.cv f) (.cv a) (.cv b))) (.classMem (syn_crn (.cv f)) (syn_cnc (.cv x))) (syn_wss (syn_crn (.cv f)) (.cv b)) (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) p0040 p0044 p0046
  have p0048 :=
    @g_ex (.classMem (.cv a) (syn_cnc (.cv x))) (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) p0047
  have p0049 :=
    @g_exlimdv (.classMem (.cv a) (syn_cnc (.cv x))) (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) f dv_cache_0019 dv_cache_0020 p0048
  have p0050 :=
    @g_rexlimiv (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))) (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) a (syn_cnc (.cv x)) dv_cache_0021 p0049
  have p0051 :=
    @g_impbii (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) p0024 p0050
  have p0052 :=
    @g_rexbii (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b))) (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) b (syn_cnc (.cv y)) p0051
  have p0053 :=
    @g_bitri (syn_wrex c (syn_cnc (.cv x)) (syn_wrex b (syn_cnc (.cv y)) (syn_wss (.cv c) (.cv b)))) (syn_wrex b (syn_cnc (.cv y)) (syn_wrex c (syn_cnc (.cv x)) (syn_wss (.cv c) (.cv b)))) (syn_wrex b (syn_cnc (.cv y)) (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))) p0008 p0052
  have p0054 :=
    @g_rexcom (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))) b a (syn_cnc (.cv y)) (syn_cnc (.cv x)) dv_cache_0022 dv_cache_0009 dv_cache_0023
  have p0055 :=
    @g_n_3bitri (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc (.cv y))) (syn_wrex c (syn_cnc (.cv x)) (syn_wrex b (syn_cnc (.cv y)) (syn_wss (.cv c) (.cv b)))) (syn_wrex b (syn_cnc (.cv y)) (syn_wrex a (syn_cnc (.cv x)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))) (syn_wrex a (syn_cnc (.cv x)) (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))) p0007 p0053 p0054
  have p0056 :=
    @g_breq12 M (syn_cnc (.cv x)) N (syn_cnc (.cv y)) (syn_clec)
  have p0057 :=
    @g_simpl (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))
  have p0058 :=
    @g_rexeq (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))) b N (syn_cnc (.cv y)) dv_cache_0024 dv_cache_0007
  have p0059 :=
    @g_adantl (.classEq N (syn_cnc (.cv y))) (syn_wb (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))) (.classEq M (syn_cnc (.cv x))) p0058
  have p0060 :=
    @g_rexeqbidv (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))) (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))) a M (syn_cnc (.cv x)) dv_cache_0025 dv_cache_0014 dv_cache_0026 p0057 p0059
  have p0061 :=
    @g_bibi12d (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))) (syn_wbr M (syn_clec) N) (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc (.cv y))) (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))) (syn_wrex a (syn_cnc (.cv x)) (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b))))) p0056 p0060
  have p0062 :=
    @g_mpbiri (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))) (syn_wb (syn_wbr M (syn_clec) N) (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))) (syn_wb (syn_wbr (syn_cnc (.cv x)) (syn_clec) (syn_cnc (.cv y))) (syn_wrex a (syn_cnc (.cv x)) (syn_wrex b (syn_cnc (.cv y)) (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))) p0055 p0061
  have p0063 :=
    @g_exlimivv (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))) (syn_wb (syn_wbr M (syn_clec) N) (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))) x y dv_cache_0027 dv_cache_0028 p0062
  have p0064 :=
    @g_sylbi (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wex x (syn_wex y (syn_wa (.classEq M (syn_cnc (.cv x))) (.classEq N (syn_cnc (.cv y)))))) (syn_wb (syn_wbr M (syn_clec) N) (syn_wrex a M (syn_wrex b N (syn_wex f (syn_wf1 (.cv f) (.cv a) (.cv b)))))) p0004 p0063
  exact p0064

#print axioms g_dflec3

end NFChoice.DirectNominalPrf.WPPReplay
