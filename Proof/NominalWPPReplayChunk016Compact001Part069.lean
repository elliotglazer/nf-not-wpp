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
import NominalWPPReplayChunk016Compact001Part068

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

noncomputable def g_hndownmpteqdv
    (x : Var) (y : Var) (z : Var) (D : Class) (g : Var) (E : Class) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_E_y : y ∉ E.fv) (dv_E_z : z ∉ E.fv) (dv_g_x : g ≠ x) (dv_g_y : g ≠ y) (dv_g_z : g ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classEq (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ D.fv ∪ ({g} : Finset Var) ∪ E.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_ne_g : a ≠ g := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_a : g ≠ a :=
    Ne.symm fresh_a_ne_g
  have fresh_a_not_E : a ∉ E.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_b_ne_z : b ≠ z := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_b : z ≠ b :=
    Ne.symm fresh_b_ne_z
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_g : b ≠ g := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_b : g ≠ b :=
    Ne.symm fresh_b_ne_g
  have fresh_b_not_E : b ∉ E.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : a ≠ x := by
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0002 : a ≠ y := by
    clear dv_cache_0001
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0003 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0004 : b ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0005 : g ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show g ≠ x from (by exact dv_g_x))
  have dv_cache_0006 : g ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show g ≠ y from (by exact dv_g_y))
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : z ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, (Ne.symm dv_g_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : g ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show g ≠ z from (by exact dv_g_z))
  have dv_cache_0013 : a ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : b ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_D, fresh_a_ne_z, fresh_a_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ ((syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_D, fresh_b_ne_z, fresh_b_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_D, fresh_a_not_E, fresh_a_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_D, fresh_b_not_E, fresh_b_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))))
  have p0001 :=
    @g_a1i (syn_wb (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0000
  have p0002 :=
    @g_bicomd (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) p0001
  have p0003 :=
    @g_hndownbrndv x y g a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @g_a1i (syn_wb (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0003
  have p0005 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
  have p0006 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
  have p0007 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
  have p0008 :=
    @g_breldm (syn_csn (.cv a)) (syn_csn (.cv b)) (.cv g)
  have p0009 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (.classMem (syn_csn (.cv a)) (syn_cdm (.cv g))) p0007 p0008
  have p0010 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
  have p0011 :=
    @g_f1odm (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0012 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classEq (syn_cdm (.cv g)) (syn_cpw1 D)) p0010 p0011
  have p0013 :=
    @g_eleqtrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) (syn_csn (.cv a)) (syn_cdm (.cv g)) (syn_cpw1 D) p0009 p0012
  have p0014 :=
    @g_snelpw1 (.cv a) D
  have p0015 :=
    @g_biimpi (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (.cv a) D) p0014
  have p0016 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (.cv a) D) p0013 p0015
  have p0017 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D) p0006 p0016
  have p0018 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0019 :=
    @g_f1ofn (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0020 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wfn (.cv g) (syn_cpw1 D)) p0018 p0019
  have p0021 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0022 :=
    @g_snelpw1 (.cv a) D
  have p0023 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classMem (.cv a) D) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0021 p0022
  have p0024 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wfn (.cv g) (syn_cpw1 D)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0020 p0023
  have p0025 :=
    @g_fnbrfvb (syn_cpw1 D) (syn_csn (.cv a)) (syn_csn (.cv b)) (.cv g)
  have p0026 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wa (syn_wfn (.cv g) (syn_cpw1 D)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D))) (syn_wb (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) p0024 p0025
  have p0027 :=
    @g_bicomd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) p0026
  have p0028 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0029 :=
    @g_f1of (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0030 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0028 p0029
  have p0031 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0032 :=
    @g_snelpw1 (.cv a) D
  have p0033 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classMem (.cv a) D) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0031 p0032
  have p0034 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0030 p0033
  have p0035 :=
    @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv a)) (.cv g)
  have p0036 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D))) (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E)) p0034 p0035
  have p0037 :=
    @g_pw1argclcl E (syn_cfv (.cv g) (syn_csn (.cv a)))
  have p0038 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E)) (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))))) p0036 p0037
  have p0039 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))))
  have p0040 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))))) p0038 p0039
  have p0041 :=
    @g_eqeq1d (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) (syn_csn (.cv b)) p0040
  have p0042 :=
    @g_fvex (syn_csn (.cv a)) (.cv g)
  have p0043 :=
    @g_uniex (syn_cfv (.cv g) (syn_csn (.cv a))) p0042
  have p0044 :=
    @g_sneqb (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b) p0043
  have p0045 :=
    @g_a1i (syn_wb (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) (syn_csn (.cv b))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b))) (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) p0044
  have p0046 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b))) (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) (syn_csn (.cv b))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) p0041 p0045
  have p0047 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) p0027 p0046
  have p0048 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0049 :=
    @g_id (.classEq (.cv z) (.cv a))
  have p0050 :=
    @g_sneqd (.classEq (.cv z) (.cv a)) (.cv z) (.cv a) p0049
  have p0051 :=
    @g_fveq2d (.classEq (.cv z) (.cv a)) (syn_csn (.cv z)) (syn_csn (.cv a)) (.cv g) p0050
  have p0052 :=
    @g_unieqd (.classEq (.cv z) (.cv a)) (syn_cfv (.cv g) (syn_csn (.cv z))) (syn_cfv (.cv g) (syn_csn (.cv a))) p0051
  have p0053 :=
    @g_eqid (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0054 :=
    @g_fvex (syn_csn (.cv a)) (.cv g)
  have p0055 :=
    @g_uniex (syn_cfv (.cv g) (syn_csn (.cv a))) p0054
  have p0056 :=
    @g_fvmpt z (.cv a) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) D (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0052 p0053 p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classMem (.cv a) D) (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) p0048 p0056
  have p0058 :=
    @g_eqeq1d (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b) p0057
  have p0059 :=
    @g_bicomd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (.cv b)) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) p0058
  have p0060 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0061 :=
    @g_pw1descentf1odv z D g E dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0062 :=
    @g_f1ofn D E (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0063 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E) (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) p0061 p0062
  have p0064 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) p0060 p0063
  have p0065 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0066 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) (.classMem (.cv a) D) p0064 p0065
  have p0067 :=
    @g_fnbrfvb D (.cv a) (.cv b) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0068 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wa (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) (.classMem (.cv a) D)) (syn_wb (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (.cv b)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) p0066 p0067
  have p0069 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (.cv b)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0059 p0068
  have p0070 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0047 p0069
  have p0071 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wb (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) p0017 p0070
  have p0072 :=
    @g_biimpd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0071
  have p0073 :=
    @g_mpd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0005 p0072
  have p0074 :=
    @g_ex (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0073
  have p0075 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
  have p0076 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
  have p0077 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
  have p0078 :=
    @g_breldm (.cv a) (.cv b) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0079 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) (.classMem (.cv a) (syn_cdm (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))))) p0077 p0078
  have p0080 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
  have p0081 :=
    @g_pw1descentf1odv z D g E dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0082 :=
    @g_f1odm D E (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0083 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E) (.classEq (syn_cdm (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))) D) p0081 p0082
  have p0084 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classEq (syn_cdm (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))) D) p0080 p0083
  have p0085 :=
    @g_eleqtrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) (.cv a) (syn_cdm (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))) D p0079 p0084
  have p0086 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D) p0076 p0085
  have p0087 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0088 :=
    @g_f1ofn (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0089 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wfn (.cv g) (syn_cpw1 D)) p0087 p0088
  have p0090 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0091 :=
    @g_snelpw1 (.cv a) D
  have p0092 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classMem (.cv a) D) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0090 p0091
  have p0093 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wfn (.cv g) (syn_cpw1 D)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0089 p0092
  have p0094 :=
    @g_fnbrfvb (syn_cpw1 D) (syn_csn (.cv a)) (syn_csn (.cv b)) (.cv g)
  have p0095 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wa (syn_wfn (.cv g) (syn_cpw1 D)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D))) (syn_wb (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) p0093 p0094
  have p0096 :=
    @g_bicomd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) p0095
  have p0097 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0098 :=
    @g_f1of (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0099 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0097 p0098
  have p0100 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0101 :=
    @g_snelpw1 (.cv a) D
  have p0102 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classMem (.cv a) D) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0100 p0101
  have p0103 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0099 p0102
  have p0104 :=
    @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv a)) (.cv g)
  have p0105 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D))) (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E)) p0103 p0104
  have p0106 :=
    @g_pw1argclcl E (syn_cfv (.cv g) (syn_csn (.cv a)))
  have p0107 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E)) (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))))) p0105 p0106
  have p0108 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))))
  have p0109 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) E) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))))) p0107 p0108
  have p0110 :=
    @g_eqeq1d (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) (syn_csn (.cv b)) p0109
  have p0111 :=
    @g_fvex (syn_csn (.cv a)) (.cv g)
  have p0112 :=
    @g_uniex (syn_cfv (.cv g) (syn_csn (.cv a))) p0111
  have p0113 :=
    @g_sneqb (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b) p0112
  have p0114 :=
    @g_a1i (syn_wb (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) (syn_csn (.cv b))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b))) (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) p0113
  have p0115 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b))) (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) (syn_csn (.cv b))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) p0110 p0114
  have p0116 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) p0096 p0115
  have p0117 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0118 :=
    @g_id (.classEq (.cv z) (.cv a))
  have p0119 :=
    @g_sneqd (.classEq (.cv z) (.cv a)) (.cv z) (.cv a) p0118
  have p0120 :=
    @g_fveq2d (.classEq (.cv z) (.cv a)) (syn_csn (.cv z)) (syn_csn (.cv a)) (.cv g) p0119
  have p0121 :=
    @g_unieqd (.classEq (.cv z) (.cv a)) (syn_cfv (.cv g) (syn_csn (.cv z))) (syn_cfv (.cv g) (syn_csn (.cv a))) p0120
  have p0122 :=
    @g_eqid (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0123 :=
    @g_fvex (syn_csn (.cv a)) (.cv g)
  have p0124 :=
    @g_uniex (syn_cfv (.cv g) (syn_csn (.cv a))) p0123
  have p0125 :=
    @g_fvmpt z (.cv a) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) D (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0121 p0122 p0124
  have p0126 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classMem (.cv a) D) (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) p0117 p0125
  have p0127 :=
    @g_eqeq1d (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b) p0126
  have p0128 :=
    @g_bicomd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (.cv b)) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) p0127
  have p0129 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0130 :=
    @g_pw1descentf1odv z D g E dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0131 :=
    @g_f1ofn D E (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0132 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E) (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) p0130 p0131
  have p0133 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) p0129 p0132
  have p0134 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0135 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) (.classMem (.cv a) D) p0133 p0134
  have p0136 :=
    @g_fnbrfvb D (.cv a) (.cv b) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0137 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wa (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) (.classMem (.cv a) D)) (syn_wb (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (.cv b)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) p0135 p0136
  have p0138 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) (.cv b)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0128 p0137
  have p0139 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0116 p0138
  have p0140 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) (syn_wb (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) p0086 p0139
  have p0141 :=
    @g_biimprd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0140
  have p0142 :=
    @g_mpd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) p0075 p0141
  have p0143 :=
    @g_ex (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) p0142
  have p0144 :=
    @g_impbid (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0074 p0143
  have p0145 :=
    @g_bitrd (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)) (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0004 p0144
  have p0146 :=
    @g_bitrd (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (syn_wbr (.cv a) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) p0002 p0145
  have p0147 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))))
  have p0148 :=
    @g_a1i (syn_wb (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))))) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0147
  have p0149 :=
    @g_bitrd (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))) p0146 p0148
  have p0150 :=
    @g_eqrelrdv (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) a b (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0149
  exact p0150

noncomputable def g_pw1isoexequivndv
    (D : Class) (R : Class) (S : Class) (f : Var) (g : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_g : g ∉ D.fv) (dv_E_f : f ∉ E.fv) (dv_E_g : g ∉ E.fv) (dv_R_f : f ∉ R.fv) (dv_R_g : g ∉ R.fv) (dv_S_f : f ∉ S.fv) (dv_S_g : g ∉ S.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf (syn_wb (syn_wex f (syn_wiso (.cv f) R S D E)) (syn_wex g (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ ({f} : Finset Var) ∪ ({g} : Finset Var) ∪ E.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_ne_g : x ≠ g := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_x : g ≠ x :=
    Ne.symm fresh_x_ne_g
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_y : g ≠ y :=
    Ne.symm fresh_y_ne_g
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_f_ne_z : f ≠ z :=
    Ne.symm fresh_z_ne_f
  have fresh_z_ne_g : z ≠ g := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_z : g ≠ z :=
    Ne.symm fresh_z_ne_g
  have fresh_z_not_E : z ∉ E.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : g ∉ ((syn_csi (.cv f))).fv := by
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_f_g), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : g ∉ ((syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_g, dv_E_g, (Ne.symm dv_f_g), dv_R_g, dv_S_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_wex g (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_f, dv_E_f, dv_f_g, dv_R_f, dv_S_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : g ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show g ≠ z from (by exact fresh_g_ne_z))
  have dv_cache_0007 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : g ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show g ≠ x from (by exact fresh_g_ne_x))
  have dv_cache_0012 : g ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0014 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0015 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0016 : f ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, dv_f_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : f ∉ ((syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_f, dv_E_f, fresh_f_ne_x, fresh_f_ne_y, dv_f_g, dv_R_f, dv_S_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : g ∉ ((syn_wex f (syn_wiso (.cv f) R S D E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_g, dv_E_g, (Ne.symm dv_f_g), dv_R_g, dv_S_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pw1raiseisomdv D R S f E
  have p0001 :=
    @g_vex f
  have p0002 :=
    @g_siex (.cv f) p0001
  have p0003 :=
    @g_isoeq1 (syn_cpw1 D) (syn_cpw1 E) (syn_csi R) (syn_csi S) (syn_csi (.cv f)) (.cv g)
  have p0004 :=
    @g_spcev (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) g (syn_csi (.cv f)) dv_cache_0001 dv_cache_0002 p0002 p0003
  have p0005 :=
    @g_syl (syn_wiso (.cv f) R S D E) (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wex g (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))) p0000 p0004
  have p0006 :=
    @g_exlimiv (syn_wiso (.cv f) R S D E) (syn_wex g (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))) f dv_cache_0003 p0005
  have p0007 :=
    @g_pw1descentisomdv z D R S g E dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 :=
    @g_isof1o (syn_cpw1 D) (syn_cpw1 E) (syn_csi R) (syn_csi S) (.cv g)
  have p0009 :=
    @g_hndownmpteqdv x y z D g E dv_cache_0007 dv_cache_0008 dv_cache_0004 dv_cache_0009 dv_cache_0010 dv_cache_0005 dv_cache_0011 dv_cache_0012 dv_cache_0006 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0010 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classEq (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))) p0008 p0009
  have p0011 :=
    @g_isoeq1 D E R S (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
  have p0012 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (.classEq (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))) (syn_wb (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E) (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E)) p0010 p0011
  have p0013 :=
    @g_biimprd (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E) (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E) p0012
  have p0014 :=
    @g_mpd (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E) (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E) p0007 p0013
  have p0015 :=
    @g_hndownexndv x y g dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0016 :=
    @g_isoeq1 D E R S (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv f)
  have p0017 :=
    @g_spcev (syn_wiso (.cv f) R S D E) (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E) f (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) dv_cache_0016 dv_cache_0017 p0015 p0016
  have p0018 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E) (syn_wex f (syn_wiso (.cv f) R S D E)) p0014 p0017
  have p0019 :=
    @g_exlimiv (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) (syn_wex f (syn_wiso (.cv f) R S D E)) g dv_cache_0018 p0018
  have p0020 :=
    @g_impbii (syn_wex f (syn_wiso (.cv f) R S D E)) (syn_wex g (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))) p0006 p0019
  exact p0020

#print axioms g_pw1isoexequivndv

end NFChoice.DirectNominalPrf.WPPReplay
