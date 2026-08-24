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
import NominalWPPReplayChunk015Compact001Part008

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

noncomputable def g_lnqordconnex
    (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr (syn_clnqord R C) (syn_cconnex) (syn_clnquo R C))) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  let v : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_ne_v : x ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_ne_v : y ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0002 : Disjoint (C).fv ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (show Disjoint (C).fv ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((C).fv) (({x} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show x ∉ (C).fv from (by exact fresh_x_not_C))))))
  have dv_cache_0003 : u ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : Disjoint ((Class.cv x)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0005 : u ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint (C).fv ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (C).fv ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((C).fv) (({y} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show y ∉ (C).fv from (by exact fresh_y_not_C))))))
  have dv_cache_0008 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : Disjoint ((Class.cv y)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint ((Class.cv y)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0010 : v ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : v ∉ ((syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_not_C, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : v ∉ ((syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_y, fresh_v_not_C, fresh_v_not_R, fresh_v_ne_x, fresh_v_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : u ∉ ((syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_not_C, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : u ∉ ((syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_y, fresh_u_not_C, fresh_u_not_R, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_clnquo R C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_clnquo R C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_clnqord R C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((syn_clnqord R C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : x ∉ ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0001 :=
    @g_lnqordexg C R dv_cache_0001
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem (syn_clnqord R C) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0004 :=
    @g_lnquoexg C R dv_cache_0001
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem (syn_clnquo R C) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_simp2 (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_ellnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0007
  have p0009 :=
    @g_biimpi (.classMem (.cv x) (syn_clnquo R C)) (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0008
  have p0010 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (.classMem (.cv x) (syn_clnquo R C)) (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0006 p0009
  have p0011 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0012 :=
    @g_simp3 (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0013 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (.classMem (.cv y) (syn_clnquo R C)) p0011 p0012
  have p0014 :=
    @g_vex y
  have p0015 :=
    @g_ellnquo v C (.cv y) R dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0014
  have p0016 :=
    @g_biimpi (.classMem (.cv y) (syn_clnquo R C)) (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) p0015
  have p0017 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classMem (.cv y) (syn_clnquo R C)) (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) p0013 p0016
  have p0018 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0019 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0020 :=
    @g_simp1 (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0021 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0019 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0018 p0021
  have p0023 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0024 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0023 p0024
  have p0026 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0027 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wbr R (syn_cconnex) C) p0025 p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr R (syn_cconnex) C) p0022 p0027
  have p0029 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0030 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0031 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0032 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classMem (.cv u) C) p0030 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classMem (.cv u) C) p0029 p0032
  have p0034 :=
    @g_simpr (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0035 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) (.classMem (.cv v) C) p0034 p0035
  have p0037 :=
    @g_connexd (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) C R (.cv u) (.cv v) p0028 p0033 p0036
  have p0038 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0039 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0040 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0041 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0039 p0040
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0038 p0041
  have p0043 :=
    @g_simpr (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0044 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0043 p0044
  have p0046 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0042 p0045
  have p0047 :=
    @g_breq12 (.cv x) (syn_cec (.cv u) (syn_clnker R)) (.cv y) (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) (syn_wb (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C) (syn_cec (.cv v) (syn_clnker R)))) p0046 p0047
  have p0049 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0050 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0051 :=
    @g_simp1 (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0052 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0050 p0051
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0049 p0052
  have p0054 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0055 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0056 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv)) p0054 p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem R (syn_cvv)) p0053 p0056
  have p0058 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0059 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0060 :=
    @g_simp1 (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0061 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0059 p0060
  have p0062 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0058 p0061
  have p0063 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0064 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0065 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0063 p0064
  have p0066 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0067 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0065 p0066
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0062 p0067
  have p0069 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0070 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0071 :=
    @g_simp1 (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0072 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0070 p0071
  have p0073 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0069 p0072
  have p0074 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0075 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0076 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wss R (syn_cxp C C)) p0074 p0075
  have p0077 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss R (syn_cxp C C)) p0073 p0076
  have p0078 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0068 p0077
  have p0079 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0080 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0081 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0082 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classMem (.cv u) C) p0080 p0081
  have p0083 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classMem (.cv u) C) p0079 p0082
  have p0084 :=
    @g_simpr (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0085 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0086 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) (.classMem (.cv v) C) p0084 p0085
  have p0087 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (.classMem (.cv u) C) (.classMem (.cv v) C) p0083 p0086
  have p0088 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)) p0078 p0087
  have p0089 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C))) p0057 p0088
  have p0090 :=
    @g_brlnqordkern C R (.cv u) (.cv v) dv_cache_0001
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C) (syn_cec (.cv v) (syn_clnker R))) (syn_wbr (.cv u) R (.cv v))) p0089 p0090
  have p0092 :=
    @g_bitrd (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C) (syn_cec (.cv v) (syn_clnker R))) (syn_wbr (.cv u) R (.cv v)) p0048 p0091
  have p0093 :=
    @g_simpr (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0094 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0095 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0093 p0094
  have p0096 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0097 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0098 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0099 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0097 p0098
  have p0100 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0096 p0099
  have p0101 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0095 p0100
  have p0102 :=
    @g_breq12 (.cv y) (syn_cec (.cv v) (syn_clnker R)) (.cv x) (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
  have p0103 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (syn_wb (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))) p0101 p0102
  have p0104 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0105 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0106 :=
    @g_simp1 (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0107 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0105 p0106
  have p0108 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0104 p0107
  have p0109 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0110 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0111 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv)) p0109 p0110
  have p0112 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem R (syn_cvv)) p0108 p0111
  have p0113 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0114 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0115 :=
    @g_simp1 (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0116 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0114 p0115
  have p0117 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0113 p0116
  have p0118 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0119 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0120 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0118 p0119
  have p0121 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0122 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0120 p0121
  have p0123 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0117 p0122
  have p0124 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0125 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0126 :=
    @g_simp1 (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0127 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0125 p0126
  have p0128 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0124 p0127
  have p0129 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0130 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0131 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wss R (syn_cxp C C)) p0129 p0130
  have p0132 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss R (syn_cxp C C)) p0128 p0131
  have p0133 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0123 p0132
  have p0134 :=
    @g_simpr (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0135 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0136 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) (.classMem (.cv v) C) p0134 p0135
  have p0137 :=
    @g_simpl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0138 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0139 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0140 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) (.classMem (.cv u) C) p0138 p0139
  have p0141 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classMem (.cv u) C) p0137 p0140
  have p0142 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (.classMem (.cv v) C) (.classMem (.cv u) C) p0136 p0141
  have p0143 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0133 p0142
  have p0144 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C))) p0112 p0143
  have p0145 :=
    @g_brlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0146 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)))) (syn_wb (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R))) (syn_wbr (.cv v) R (.cv u))) p0144 p0145
  have p0147 :=
    @g_bitrd (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R))) (syn_wbr (.cv v) R (.cv u)) p0103 p0146
  have p0148 :=
    @g_orbi12d (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv u) R (.cv v)) (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) (syn_wbr (.cv v) R (.cv u)) p0092 p0147
  have p0149 :=
    @g_mpbird (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))) (syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))) (syn_wo (syn_wbr (.cv u) R (.cv v)) (syn_wbr (.cv v) R (.cv u))) p0037 p0148
  have p0150 :=
    @g_rexlimddv (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) (syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))) v C dv_cache_0012 dv_cache_0013 p0017 p0149
  have p0151 :=
    @g_rexlimddv (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) (syn_wo (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))) u C dv_cache_0014 dv_cache_0015 p0010 p0150
  have p0152 :=
    @g_connexrd (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) x y (syn_clnquo R C) (syn_clnqord R C) (syn_cvv) (syn_cvv) dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 p0002 p0005 p0151
  exact p0152

#print axioms g_lnqordconnex

end NFChoice.DirectNominalPrf.WPPReplay
