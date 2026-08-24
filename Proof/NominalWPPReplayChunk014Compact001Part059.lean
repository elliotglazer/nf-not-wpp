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
import NominalWPPReplayChunk014Compact001Part058

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

noncomputable def g_finlefr
     :
    Nominal.NPrf (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
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
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_v : y ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have fresh_w_ne_v : w ≠ v := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_v_ne_w : v ≠ w :=
    Ne.symm fresh_w_ne_v
  have dv_cache_0001 : v ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have dv_cache_0006 : v ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_w, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq (.cv z) (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classEq (.cv y) (.cv z)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0023 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0024 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_tru
  have p0001 :=
    @g_lefinex
  have p0002 :=
    @g_kqrelex (syn_clefin) p0001
  have p0003 :=
    @g_a1i (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) syn_wtru p0002
  have p0004 :=
    @g_nncex
  have p0005 :=
    @g_a1i (.classMem (syn_cnnc) (syn_cvv)) syn_wtru p0004
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) p0006
  have p0008 :=
    @g_simpr syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
  have p0009 :=
    @g_simpl (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))
  have p0010 :=
    @g_syl (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) (syn_cnnc)) p0008 p0009
  have p0011 :=
    @g_simpr syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
  have p0012 :=
    @g_simpr (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))
  have p0013 :=
    @g_syl (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))) (syn_wne (.cv x) (syn_c0)) p0011 p0012
  have p0014 :=
    @g_n_3jca (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv x) (syn_cvv)) (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)) p0007 p0010 p0013
  have p0015 :=
    @g_finleastnn v w (syn_cvv) (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0016 :=
    @g_syl (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_w3a (.classMem (.cv x) (syn_cvv)) (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))) (syn_wrex w (.cv x) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) p0014 p0015
  have p0017 :=
    @g_simpl (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
  have p0018 :=
    @g_simpr (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (.classMem (.cv w) (.cv x)) p0017 p0018
  have p0020 :=
    @g_finleor
  have p0021 :=
    @g_sopc (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0022 :=
    @g_biimpi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc)) (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc))) p0021
  have p0023 :=
    Nominal.mp p0020 p0022
  have p0024 :=
    @g_simpl (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_porta (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0027 :=
    @g_biimpi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc)) (syn_w3a (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))) p0026
  have p0028 :=
    Nominal.mp p0025 p0027
  have p0029 :=
    @g_simp3 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))) p0030
  have p0032 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
  have p0033 :=
    @g_simpl (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))
  have p0034 :=
    @g_simpl (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
  have p0035 :=
    @g_simpl (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))
  have p0036 :=
    @g_simpr syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
  have p0037 :=
    @g_simpl (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))
  have p0038 :=
    @g_syl (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) (syn_cnnc)) p0036 p0037
  have p0039 :=
    @g_syl (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) (syn_cnnc)) p0035 p0038
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wss (.cv x) (syn_cnnc)) p0034 p0039
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (syn_wss (.cv x) (syn_cnnc)) p0033 p0040
  have p0042 :=
    @g_simpr (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))
  have p0043 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (.cv x) (syn_cnnc) (.cv y) p0041 p0042
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))) (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (.classMem (.cv y) (syn_cnnc)) p0032 p0043
  have p0045 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
  have p0046 :=
    @g_simpl (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))
  have p0047 :=
    @g_simpl (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
  have p0048 :=
    @g_simpl (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))
  have p0049 :=
    @g_simpr syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
  have p0050 :=
    @g_simpl (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))
  have p0051 :=
    @g_syl (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))) (syn_wss (.cv x) (syn_cnnc)) p0049 p0050
  have p0052 :=
    @g_syl (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) (syn_cnnc)) p0048 p0051
  have p0053 :=
    @g_simpr (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))
  have p0054 :=
    @g_sseldd (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (.cv x) (syn_cnnc) (.cv w) p0052 p0053
  have p0055 :=
    @g_syl (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (.classMem (.cv w) (syn_cnnc)) p0047 p0054
  have p0056 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv w) (syn_cnnc)) p0046 p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))) (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (.classMem (.cv w) (syn_cnnc)) p0045 p0056
  have p0058 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
  have p0059 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
  have p0060 :=
    @g_simpl (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))
  have p0061 :=
    @g_simpr (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
  have p0062 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))) p0060 p0061
  have p0063 :=
    @g_simpr (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))
  have p0064 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))) (.classMem (.cv y) (.cv x)) p0062 p0063
  have p0065 :=
    @g_breq2 (.cv v) (.cv y) (.cv w) (syn_ckqrel (syn_clefin))
  have p0066 :=
    @g_rspccva (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv y)) v (.cv y) (.cv x) dv_cache_0006 dv_cache_0003 dv_cache_0007 p0065
  have p0067 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wa (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv y)) p0064 p0066
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))) (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv y)) p0059 p0067
  have p0069 :=
    @g_antid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))) (syn_cnnc) (syn_ckqrel (syn_clefin)) (.cv y) (.cv w) p0031 p0044 p0057 p0058 p0068
  have p0070 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w)) p0069
  have p0071 :=
    @g_ralrimiva (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w))) y (.cv x) dv_cache_0008 p0070
  have p0072 :=
    @g_jca (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (.classMem (.cv w) (.cv x)) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w)))) p0019 p0071
  have p0073 :=
    @g_breq2 (.cv z) (.cv w) (.cv y) (syn_ckqrel (syn_clefin))
  have p0074 :=
    @g_eqeq2 (.cv z) (.cv w) (.cv y)
  have p0075 :=
    @g_imbi12d (.classEq (.cv z) (.cv w)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv z)) (.classEq (.cv y) (.cv w)) p0073 p0074
  have p0076 :=
    @g_ralbidv (.classEq (.cv z) (.cv w)) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classEq (.cv y) (.cv z))) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w))) y (.cv x) dv_cache_0009 p0075
  have p0077 :=
    @g_rspcev (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classEq (.cv y) (.cv z)))) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w)))) z (.cv w) (.cv x) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0076
  have p0078 :=
    @g_syl (syn_wa (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (syn_wa (.classMem (.cv w) (.cv x)) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w))))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classEq (.cv y) (.cv z))))) p0072 p0077
  have p0079 :=
    @g_ex (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (.classMem (.cv w) (.cv x))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classEq (.cv y) (.cv z))))) p0078
  have p0080 :=
    @g_rexlimdva (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classEq (.cv y) (.cv z))))) w (.cv x) dv_cache_0013 dv_cache_0014 p0079
  have p0081 :=
    @g_mpd (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_wrex w (.cv x) (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classEq (.cv y) (.cv z))))) p0016 p0080
  have p0082_e02_recanon : Nominal.NPrf (.imp (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wtru syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_ckqrel syn_copab syn_copk syn_cpr syn_csn syn_clefin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0081
  have p0082 :=
    @g_frrd syn_wtru x y z (syn_cnnc) (syn_ckqrel (syn_clefin)) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0003 p0005 p0082_e02_recanon
  have p0083 :=
    Nominal.mp p0000 p0082
  exact p0083

noncomputable def g_finlewe
     :
    Nominal.NPrf (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_tru
  have p0001 :=
    @g_finleor
  have p0002 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc)) syn_wtru p0001
  have p0003 :=
    @g_finlefr
  have p0004 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc)) syn_wtru p0003
  have p0005 :=
    @g_jca syn_wtru (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc)) p0002 p0004
  have p0006 :=
    Nominal.mp p0000 p0005
  have p0007 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0008 :=
    @g_breqi (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0007
  have p0009 :=
    @g_brin (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cstrict) (syn_cfound)
  have p0010 :=
    @g_bitri (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cin (syn_cstrict) (syn_cfound)) (syn_cnnc)) (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc))) p0008 p0009
  have p0011 :=
    @g_mpbir (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc))) p0006 p0010
  exact p0011

noncomputable def g_wpporbit0
    (F : Class) (I : Class) (dv_F_I : Disjoint F.fv I.fv) :
    Nominal.NPrf (.imp (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classEq (syn_cfv (syn_cfrec F I) (syn_c0c)) I)) := by
  let proofSupport : Finset Var := F.fv ∪ I.fv
  have p0000 :=
    @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0002 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0004 :=
    @g_frec0 (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0000 p0001 p0002 p0003
  exact p0004

noncomputable def g_wpporbitsuc
    (F : Class) (I : Class) (N : Class) (dv_F_I : Disjoint F.fv I.fv) (dv_F_N : Disjoint F.fv N.fv) (dv_I_N : Disjoint I.fv N.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))) := by
  let proofSupport : Finset Var := F.fv ∪ I.fv ∪ N.fv
  have p0000 :=
    @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0002 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem F (syn_cfuns)) p0001 p0002
  have p0004 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0005 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0006 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem I (syn_cdm F)) p0004 p0005
  have p0007 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0008 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0009 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wss (syn_crn F) (syn_cdm F)) p0007 p0008
  have p0010 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0011 :=
    @g_frecsuc (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_cfrec F I) F I N p0000 p0003 p0006 p0009 p0010
  exact p0011

noncomputable def g_kqfinsucnle
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (.neg (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_elex A (syn_cnnc)
  have p0001 :=
    @g_id (.classMem A (syn_cnnc))
  have p0002 :=
    @g_nulnnn
  have p0003 :=
    @g_a1i (.neg (.classMem (syn_c0) (syn_cnnc))) (.classMem A (syn_cnnc)) p0002
  have p0004 :=
    @g_jca (.classMem A (syn_cnnc)) (.classMem A (syn_cnnc)) (.neg (.classMem (syn_c0) (syn_cnnc))) p0001 p0003
  have p0005 :=
    @g_nelne2 A (syn_c0) (syn_cnnc)
  have p0006 :=
    @g_syl (.classMem A (syn_cnnc)) (syn_wa (.classMem A (syn_cnnc)) (.neg (.classMem (syn_c0) (syn_cnnc)))) (syn_wne A (syn_c0)) p0004 p0005
  have p0007 :=
    @g_jca (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) (syn_wne A (syn_c0)) p0000 p0006
  have p0008 :=
    @g_ltfinp1 A (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cnnc)) (syn_wa (.classMem A (syn_cvv)) (syn_wne A (syn_c0))) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin)) p0007 p0008
  have p0010 :=
    @g_notnot1 (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0011 :=
    @g_syl (.classMem A (syn_cnnc)) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin)) (.neg (.neg (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin)))) p0009 p0010
  have p0012 :=
    @g_peano2 A
  have p0013 :=
    @g_id (.classMem A (syn_cnnc))
  have p0014 :=
    @g_jca (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem A (syn_cnnc)) p0012 p0013
  have p0015 :=
    @g_lenltfin (syn_cplc A (syn_c1c)) A
  have p0016 :=
    @g_syl (.classMem A (syn_cnnc)) (syn_wa (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem A (syn_cnnc))) (syn_wb (.classMem (syn_copk (syn_cplc A (syn_c1c)) A) (syn_clefin)) (.neg (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin)))) p0014 p0015
  have p0017 :=
    @g_mtbird (.classMem A (syn_cnnc)) (.classMem (syn_copk (syn_cplc A (syn_c1c)) A) (syn_clefin)) (.neg (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))) p0011 p0016
  have p0018 :=
    @g_peano2 A
  have p0019 :=
    @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0020 :=
    @g_syl (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_elex A (syn_cnnc)
  have p0022 :=
    @g_jca (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (.classMem A (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_kqlefinbr (syn_cplc A (syn_c1c)) A (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_syl (.classMem A (syn_cnnc)) (syn_wa (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (.classMem A (syn_cvv))) (syn_wb (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk (syn_cplc A (syn_c1c)) A) (syn_clefin))) p0022 p0023
  have p0025 :=
    @g_mtbird (.classMem A (syn_cnnc)) (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk (syn_cplc A (syn_c1c)) A) (syn_clefin)) p0017 p0024
  exact p0025

#print axioms g_kqfinsucnle

end NFChoice.DirectNominalPrf.WPPReplay
