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
import NominalWPPReplayChunk014Compact001Part008

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

noncomputable def g_fdprj0valV
    (x : Var) (C : Class) (D : Class) (dv_C_D : Disjoint C.fv D.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (.classEq (.cv x) (syn_csn (syn_csn C))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ D.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
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
  have dv_cache_0003 : c ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_C, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_C, fresh_b_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : c ∉ ((syn_copk C D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, fresh_c_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((syn_cidk)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((syn_cidk)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : c ∉ ((syn_cidk)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0011 : a ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ c from (by exact fresh_a_ne_c))
  have dv_cache_0012 : b ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0013 : a ∉ ((syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_C, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : b ∉ ((syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_C, fresh_b_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : c ∉ ((syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, fresh_c_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : c ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : c ∉ ((syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_a, fresh_c_ne_b, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : b ∉ ((syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, fresh_b_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((Wff.classEq (.cv x) (syn_csn (syn_csn C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cfdprj0] using (Nominal.classEqRefl (syn_cfdprj0)))
  have p0001 :=
    @g_eleq2i (syn_cfdprj0) (syn_cins3k (syn_cidk)) (syn_copk (.cv x) (syn_copk C D)) p0000
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_opkex C D
  have p0004 :=
    @g_opkelins3kg a b c (.cv x) (syn_copk C D) (syn_cidk) (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0005 :=
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem (syn_copk C D) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cins3k (syn_cidk))) (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c))) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk))))))) p0002 p0003 p0004
  have p0006 :=
    @g_bitri (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cins3k (syn_cidk))) (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c))) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)))))) p0001 p0005
  have p0007 :=
    @g_a1i (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c))) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk))))))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0006
  have p0008 :=
    @g_biid (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
  have p0009 :=
    @g_a1i (syn_wb (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0008
  have p0010 :=
    @g_vex c
  have p0011 :=
    @g_opkthg C D (.cv b) (.cv c) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0012 :=
    @g_mp3an3 (.classMem C (syn_cvv)) (.classMem D (syn_cvv)) (.classMem (.cv c) (syn_cvv)) (syn_wb (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c))) (syn_wa (.classEq C (.cv b)) (.classEq D (.cv c)))) p0010 p0011
  have p0013 :=
    @g_eqcom C (.cv b)
  have p0014 :=
    @g_eqcom D (.cv c)
  have p0015 :=
    @g_anbi12i (.classEq C (.cv b)) (.classEq (.cv b) C) (.classEq D (.cv c)) (.classEq (.cv c) D) p0013 p0014
  have p0016 :=
    @g_a1i (syn_wb (syn_wa (.classEq C (.cv b)) (.classEq D (.cv c))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0015
  have p0017 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c))) (syn_wa (.classEq C (.cv b)) (.classEq D (.cv c))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) p0012 p0016
  have p0018 :=
    @g_vex a
  have p0019 :=
    @g_vex b
  have p0020 :=
    @g_opkelidkg (.cv a) (.cv b) (syn_cvv) (syn_cvv)
  have p0021 :=
    @g_mp2an (.classMem (.cv a) (syn_cvv)) (.classMem (.cv b) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)) (.classEq (.cv a) (.cv b))) p0018 p0019 p0020
  have p0022 :=
    @g_a1i (syn_wb (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)) (.classEq (.cv a) (.cv b))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0021
  have p0023 :=
    @g_n_3anbi123d (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)) (.classEq (.cv a) (.cv b)) p0009 p0017 p0022
  have p0024 :=
    @g_n_3exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c))) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk))) (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))) a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0023
  have p0025 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c))) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)))))) (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))))) p0007 p0024
  have p0026 :=
    @g_n_3anass (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))
  have p0027 :=
    @g_anass (.classEq (.cv b) C) (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))
  have p0028 :=
    @g_anbi2i (syn_wa (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))) (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b)))) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) p0027
  have p0029 :=
    @g_bitri (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))))) p0026 p0028
  have p0030 :=
    @g_an12 (.classEq (.cv b) C) (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))
  have p0031 :=
    @g_anbi2i (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b)))) (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) p0030
  have p0032 :=
    @g_bitri (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))) p0029 p0031
  have p0033 :=
    @g_an12 (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv c) D) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))
  have p0034 :=
    @g_bitri (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))) (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))) p0032 p0033
  have p0035 :=
    @g_a1i (syn_wb (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))) (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0034
  have p0036 :=
    @g_n_3exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))) (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))) a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0035
  have p0037 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))))) (syn_wex a (syn_wex b (syn_wex c (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))))) p0025 p0036
  have p0038 :=
    @g_simpr (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
  have p0039 :=
    @g_biidd (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
  have p0040 :=
    @g_ceqsexgv (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))) c D (syn_cvv) dv_cache_0016 dv_cache_0017 p0039
  have p0041 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem D (syn_cvv)) (syn_wb (syn_wex c (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))) p0038 p0040
  have p0042 :=
    @g_n_2exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wex c (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))) a b dv_cache_0013 dv_cache_0014 p0041
  have p0043 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (syn_wex a (syn_wex b (syn_wex c (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))) p0037 p0042
  have p0044 :=
    @g_an12 (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))
  have p0045 :=
    @g_a1i (syn_wb (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))) (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b))))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0044
  have p0046 :=
    @g_n_2exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))) (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b)))) a b dv_cache_0013 dv_cache_0014 p0045
  have p0047 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b)))))) p0043 p0046
  have p0048 :=
    @g_simpl (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
  have p0049 :=
    @g_eqeq2 (.cv b) C (.cv a)
  have p0050 :=
    @g_anbi2d (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)) (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) p0049
  have p0051 :=
    @g_ceqsexgv (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)) b C (syn_cvv) dv_cache_0018 dv_cache_0019 p0050
  have p0052 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem C (syn_cvv)) (syn_wb (syn_wex b (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b))))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C))) p0048 p0051
  have p0053 :=
    @g_exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wex b (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b))))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)) a dv_cache_0013 p0052
  have p0054 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b)))))) (syn_wex a (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C))) p0047 p0053
  have p0055 :=
    @g_ancom (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)
  have p0056 :=
    @g_exbii (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)) (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))) a p0055
  have p0057 :=
    @g_a1i (syn_wb (syn_wex a (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C))) (syn_wex a (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))))) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0056
  have p0058 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (syn_wex a (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C))) (syn_wex a (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))))) p0054 p0057
  have p0059 :=
    @g_simpl (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
  have p0060 :=
    @g_sneq (.cv a) C
  have p0061 :=
    @g_sneqd (.classEq (.cv a) C) (syn_csn (.cv a)) (syn_csn C) p0060
  have p0062 :=
    @g_eqeq2d (.classEq (.cv a) C) (syn_csn (syn_csn (.cv a))) (syn_csn (syn_csn C)) (.cv x) p0061
  have p0063 :=
    @g_ceqsexgv (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv x) (syn_csn (syn_csn C))) a C (syn_cvv) dv_cache_0020 dv_cache_0021 p0062
  have p0064 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem C (syn_cvv)) (syn_wb (syn_wex a (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))))) (.classEq (.cv x) (syn_csn (syn_csn C)))) p0059 p0063
  have p0065 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (syn_wex a (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))))) (.classEq (.cv x) (syn_csn (syn_csn C))) p0058 p0064
  exact p0065

noncomputable def g_fde0valJp
    (A : Class) (B : Class) (C : Class) (D : Class) (e : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_e : e ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_e : e ∉ C.fv) (dv_D_e : e ∉ D.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem C B) (.classMem D B)) (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ ({e} : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_e : x ≠ e := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_e_ne_x : e ≠ x :=
    Ne.symm fresh_x_ne_e
  have dv_cache_0001 : x ∉ ((syn_csn (.cv e))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_copk C D)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cfdprj0)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdprj0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cfdmem)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : Disjoint (C).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0006 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_wa (.classMem C B) (.classMem D B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_B, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_csn (syn_csn C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_e, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cfde0] using (Nominal.classEqRefl (syn_cfde0 A B)))
  have p0001 :=
    @g_eleq2i (syn_cfde0 A B) (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)) (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0000
  have p0002 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)))) (syn_wa (.classMem C B) (.classMem D B)) p0001
  have p0003 :=
    @g_elin (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)
  have p0004 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B))) (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)))) (syn_wa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B))) (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))) p0002 p0004
  have p0006 :=
    @g_snex (.cv e)
  have p0007 :=
    @g_opkex C D
  have p0008 :=
    @g_opkelcok x (syn_csn (.cv e)) (syn_copk C D) (syn_cfdprj0) (syn_cfdmem) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))))) (syn_wa (.classMem C B) (.classMem D B)) p0008
  have p0010 :=
    @g_biid (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
  have p0011 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))) (syn_wa (.classMem C B) (.classMem D B)) p0010
  have p0012 :=
    @g_simpl (.classMem C B) (.classMem D B)
  have p0013 :=
    @g_elex C B
  have p0014 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem C B) (.classMem C (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_simpr (.classMem C B) (.classMem D B)
  have p0016 :=
    @g_elex D B
  have p0017 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem D B) (.classMem D (syn_cvv)) p0015 p0016
  have p0018 :=
    @g_jca (syn_wa (.classMem C B) (.classMem D B)) (.classMem C (syn_cvv)) (.classMem D (syn_cvv)) p0014 p0017
  have p0019 :=
    @g_fdprj0valV x C D dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0020 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (.classEq (.cv x) (syn_csn (syn_csn C)))) p0018 p0019
  have p0021 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (.classEq (.cv x) (syn_csn (syn_csn C))) p0011 p0020
  have p0022 :=
    @g_exbidv (syn_wa (.classMem C B) (.classMem D B)) (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))) (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classEq (.cv x) (syn_csn (syn_csn C)))) x dv_cache_0008 p0021
  have p0023 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)))) (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classEq (.cv x) (syn_csn (syn_csn C))))) p0009 p0022
  have p0024 :=
    @g_ancom (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classEq (.cv x) (syn_csn (syn_csn C)))
  have p0025 :=
    @g_a1i (syn_wb (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classEq (.cv x) (syn_csn (syn_csn C)))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C))) (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)))) (syn_wa (.classMem C B) (.classMem D B)) p0024
  have p0026 :=
    @g_exbidv (syn_wa (.classMem C B) (.classMem D B)) (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classEq (.cv x) (syn_csn (syn_csn C)))) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C))) (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))) x dv_cache_0008 p0025
  have p0027 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classEq (.cv x) (syn_csn (syn_csn C))))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C))) (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)))) p0023 p0026
  have p0028 :=
    @g_snex (syn_csn C)
  have p0029 :=
    @g_opkeq2 (.cv x) (syn_csn (syn_csn C)) (syn_csn (.cv e))
  have p0030 :=
    @g_eleq1d (.classEq (.cv x) (syn_csn (syn_csn C))) (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem) p0029
  have p0031 :=
    @g_ceqsexgv (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) x (syn_csn (syn_csn C)) (syn_cvv) dv_cache_0009 dv_cache_0010 p0030
  have p0032 :=
    Nominal.mp p0028 p0031
  have p0033 :=
    @g_a1i (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C))) (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))) (syn_wa (.classMem C B) (.classMem D B)) p0032
  have p0034 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C))) (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) p0027 p0033
  have p0035 :=
    @g_simpl (.classMem C B) (.classMem D B)
  have p0036 :=
    @g_fdmemvalC B C e
  have p0037 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem C B) (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem C (.cv e))) p0035 p0036
  have p0038 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem C (.cv e)) p0034 p0037
  have p0039 :=
    (by simpa [syn_cfddom] using (Nominal.classEqRefl (syn_cfddom A B)))
  have p0040 :=
    @g_eleq2i (syn_cfddom A B) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)) (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0039
  have p0041 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)))) (syn_wa (.classMem C B) (.classMem D B)) p0040
  have p0042 :=
    @g_snex (.cv e)
  have p0043 :=
    @g_opkex C D
  have p0044 :=
    @g_opkelxpk (syn_csn (.cv e)) (syn_copk C D) (syn_cpw1 A) (syn_cxpk B B) p0042 p0043
  have p0045 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B))) (syn_wa (.classMem (syn_csn (.cv e)) (syn_cpw1 A)) (.classMem (syn_copk C D) (syn_cxpk B B)))) (syn_wa (.classMem C B) (.classMem D B)) p0044
  have p0046 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B))) (syn_wa (.classMem (syn_csn (.cv e)) (syn_cpw1 A)) (.classMem (syn_copk C D) (syn_cxpk B B))) p0041 p0045
  have p0047 :=
    @g_snelpw1 (.cv e) A
  have p0048 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv e)) (syn_cpw1 A)) (.classMem (.cv e) A)) (syn_wa (.classMem C B) (.classMem D B)) p0047
  have p0049 :=
    @g_simpl (.classMem C B) (.classMem D B)
  have p0050 :=
    @g_elex C B
  have p0051 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem C B) (.classMem C (syn_cvv)) p0049 p0050
  have p0052 :=
    @g_simpr (.classMem C B) (.classMem D B)
  have p0053 :=
    @g_elex D B
  have p0054 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem D B) (.classMem D (syn_cvv)) p0052 p0053
  have p0055 :=
    @g_jca (syn_wa (.classMem C B) (.classMem D B)) (.classMem C (syn_cvv)) (.classMem D (syn_cvv)) p0051 p0054
  have p0056 :=
    @g_opkelxpkg C D B B (syn_cvv) (syn_cvv)
  have p0057 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) (syn_wb (.classMem (syn_copk C D) (syn_cxpk B B)) (syn_wa (.classMem C B) (.classMem D B))) p0055 p0056
  have p0058 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_csn (.cv e)) (syn_cpw1 A)) (.classMem (.cv e) A) (.classMem (syn_copk C D) (syn_cxpk B B)) (syn_wa (.classMem C B) (.classMem D B)) p0048 p0057
  have p0059 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)) (syn_wa (.classMem (syn_csn (.cv e)) (syn_cpw1 A)) (.classMem (syn_copk C D) (syn_cxpk B B))) (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem C B) (.classMem D B))) p0046 p0058
  have p0060 :=
    @g_iba (syn_wa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A)
  have p0061 :=
    @g_bicomd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A) (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem C B) (.classMem D B))) p0060
  have p0062 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)) (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (.cv e) A) p0059 p0061
  have p0063 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (.classMem C (.cv e)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)) (.classMem (.cv e) A) p0038 p0062
  have p0064 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))) (syn_wa (.classMem C (.cv e)) (.classMem (.cv e) A)) p0005 p0063
  have p0065 :=
    @g_ancom (.classMem C (.cv e)) (.classMem (.cv e) A)
  have p0066 :=
    @g_a1i (syn_wb (syn_wa (.classMem C (.cv e)) (.classMem (.cv e) A)) (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e)))) (syn_wa (.classMem C B) (.classMem D B)) p0065
  have p0067 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)) (syn_wa (.classMem C (.cv e)) (.classMem (.cv e) A)) (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))) p0064 p0066
  exact p0067

#print axioms g_fde0valJp

end NFChoice.DirectNominalPrf.WPPReplay
