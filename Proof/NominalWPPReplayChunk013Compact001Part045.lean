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
import NominalWPPReplayChunk013Compact001Part044

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

noncomputable def g_mucnc
    (A : Class) (B : Class) (hyp_mucnc_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_mucnc_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_co (syn_cnc A) (syn_cmuc) (syn_cnc B)) (syn_cnc (syn_cxp A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
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
  have dv_cache_0001 : x ∉ ((syn_cnc A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cen)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_wa (syn_wa (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B)) (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_wa (syn_wa (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B)) (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_wbr (syn_cxp A B) (syn_cen) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_wbr (syn_cxp A B) (syn_cen) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ncelncsi A hyp_mucnc_1
  have p0001 :=
    @g_ncelncsi B hyp_mucnc_2
  have p0002 :=
    @g_ovmuc z (syn_cnc A) (syn_cnc B) x y dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0003 :=
    @g_mp2an (.classMem (syn_cnc A) (syn_cncs)) (.classMem (syn_cnc B) (syn_cncs)) (.classEq (syn_co (syn_cnc A) (syn_cmuc) (syn_cnc B)) (.cab x (syn_wrex y (syn_cnc A) (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))))))) p0000 p0001 p0002
  have p0004 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc (syn_cxp A B))))
  have p0005 :=
    @g_dfec2 x (syn_cxp A B) (syn_cen) dv_cache_0009 dv_cache_0010
  have p0006 :=
    @g_elnc (.cv y) A
  have p0007 :=
    @g_elnc (.cv z) B
  have p0008 :=
    @g_anbi12i (.classMem (.cv y) (syn_cnc A)) (syn_wbr (.cv y) (syn_cen) A) (.classMem (.cv z) (syn_cnc B)) (syn_wbr (.cv z) (syn_cen) B) p0006 p0007
  have p0009 :=
    @g_ensym (.cv x) (syn_cxp (.cv y) (.cv z))
  have p0010 :=
    @g_anbi12i (syn_wa (.classMem (.cv y) (syn_cnc A)) (.classMem (.cv z) (syn_cnc B))) (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)) p0008 p0009
  have p0011 :=
    @g_n_2exbii (syn_wa (syn_wa (.classMem (.cv y) (syn_cnc A)) (.classMem (.cv z) (syn_cnc B))) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z)))) (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x))) y z p0010
  have p0012 :=
    @g_r2ex (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))) y z (syn_cnc A) (syn_cnc B) dv_cache_0011 dv_cache_0008
  have p0013 :=
    @g_enrflx A hyp_mucnc_1
  have p0014 :=
    @g_enrflx B hyp_mucnc_2
  have p0015 :=
    @g_breq1 (.cv y) A A (syn_cen)
  have p0016 :=
    @g_breq1 (.cv z) B B (syn_cen)
  have p0017 :=
    @g_bi2anan9 (.classEq (.cv y) A) (syn_wbr (.cv y) (syn_cen) A) (syn_wbr A (syn_cen) A) (.classEq (.cv z) B) (syn_wbr (.cv z) (syn_cen) B) (syn_wbr B (syn_cen) B) p0015 p0016
  have p0018 :=
    @g_xpeq12 (.cv y) A (.cv z) B
  have p0019 :=
    @g_breq1d (syn_wa (.classEq (.cv y) A) (.classEq (.cv z) B)) (syn_cxp (.cv y) (.cv z)) (syn_cxp A B) (.cv x) (syn_cen) p0018
  have p0020 :=
    @g_anbi12d (syn_wa (.classEq (.cv y) A) (.classEq (.cv z) B)) (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wa (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B)) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)) (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) p0017 p0019
  have p0021 :=
    @g_spc2ev (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x))) (syn_wa (syn_wa (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B)) (syn_wbr (syn_cxp A B) (syn_cen) (.cv x))) y z A B dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0008 hyp_mucnc_1 hyp_mucnc_2 p0020
  have p0022 :=
    @g_mpanl12 (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B) (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x))))) p0013 p0014 p0021
  have p0023 :=
    @g_xpen (.cv y) A (.cv z) B
  have p0024 :=
    @g_ensym (syn_cxp (.cv y) (.cv z)) (syn_cxp A B)
  have p0025 :=
    @g_sylib (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (syn_cxp A B)) (syn_wbr (syn_cxp A B) (syn_cen) (syn_cxp (.cv y) (.cv z))) p0023 p0024
  have p0026 :=
    @g_entr (syn_cxp A B) (syn_cxp (.cv y) (.cv z)) (.cv x)
  have p0027 :=
    @g_sylan (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wbr (syn_cxp A B) (syn_cen) (syn_cxp (.cv y) (.cv z))) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)) (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) p0025 p0026
  have p0028 :=
    @g_exlimivv (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x))) (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) y z dv_cache_0018 dv_cache_0019 p0027
  have p0029 :=
    @g_impbii (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x))))) p0022 p0028
  have p0030 :=
    @g_n_3bitr4ri (syn_wex y (syn_wex z (syn_wa (syn_wa (.classMem (.cv y) (syn_cnc A)) (.classMem (.cv z) (syn_cnc B))) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z)))))) (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B)) (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x))))) (syn_wrex y (syn_cnc A) (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))))) (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) p0011 p0012 p0029
  have p0031 :=
    @g_abbii (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) (syn_wrex y (syn_cnc A) (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))))) x p0030
  have p0032 :=
    @g_n_3eqtrri (syn_cnc (syn_cxp A B)) (syn_cec (syn_cxp A B) (syn_cen)) (.cab x (syn_wbr (syn_cxp A B) (syn_cen) (.cv x))) (.cab x (syn_wrex y (syn_cnc A) (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z)))))) p0004 p0005 p0031
  have p0033 :=
    @g_eqtri (syn_co (syn_cnc A) (syn_cmuc) (syn_cnc B)) (.cab x (syn_wrex y (syn_cnc A) (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z)))))) (syn_cnc (syn_cxp A B)) p0003 p0032
  exact p0033

noncomputable def g_muccl
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.classMem (syn_co A (syn_cmuc) B) (syn_cncs))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_co A (syn_cmuc) B) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classMem (syn_co A (syn_cmuc) B) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs x A dv_cache_0001
  have p0001 :=
    @g_elncs y B dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x)))) (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x)))) (syn_wex y (.classEq B (syn_cnc (.cv y))))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))))) p0002 p0003
  have p0005 :=
    @g_oveq12 A (syn_cnc (.cv x)) B (syn_cnc (.cv y)) (syn_cmuc)
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_vex y
  have p0008 :=
    @g_mucnc (.cv x) (.cv y) p0006 p0007
  have p0009 :=
    @g_xpex (.cv x) (.cv y) p0006 p0007
  have p0010 :=
    @g_ncelncsi (syn_cxp (.cv x) (.cv y)) p0009
  have p0011 :=
    @g_eqeltri (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cncs) p0008 p0010
  have p0012 :=
    @g_syl6eqel (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) (syn_co A (syn_cmuc) B) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_cncs) p0005 p0011
  have p0013 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) (.classMem (syn_co A (syn_cmuc) B) (syn_cncs)) x y dv_cache_0005 dv_cache_0006 p0012
  have p0014 :=
    @g_sylbi (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))))) (.classMem (syn_co A (syn_cmuc) B) (syn_cncs)) p0004 p0013
  exact p0014

noncomputable def g_muccom
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs x A dv_cache_0001
  have p0001 :=
    @g_elncs y B dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x)))) (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x)))) (syn_wex y (.classEq B (syn_cnc (.cv y))))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))))) p0002 p0003
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_vex y
  have p0007 :=
    @g_xpcomen (.cv x) (.cv y) p0005 p0006
  have p0008 :=
    @g_xpex (.cv x) (.cv y) p0005 p0006
  have p0009 :=
    @g_eqnc (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv y) (.cv x)) p0008
  have p0010 :=
    @g_mpbir (.classEq (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cnc (syn_cxp (.cv y) (.cv x)))) (syn_wbr (syn_cxp (.cv x) (.cv y)) (syn_cen) (syn_cxp (.cv y) (.cv x))) p0007 p0009
  have p0011 :=
    @g_mucnc (.cv x) (.cv y) p0005 p0006
  have p0012 :=
    @g_mucnc (.cv y) (.cv x) p0006 p0005
  have p0013 :=
    @g_n_3eqtr4i (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cnc (syn_cxp (.cv y) (.cv x))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_co (syn_cnc (.cv y)) (syn_cmuc) (syn_cnc (.cv x))) p0010 p0011 p0012
  have p0014 :=
    @g_oveq12 A (syn_cnc (.cv x)) B (syn_cnc (.cv y)) (syn_cmuc)
  have p0015 :=
    @g_oveq12 B (syn_cnc (.cv y)) A (syn_cnc (.cv x)) (syn_cmuc)
  have p0016 :=
    @g_ancoms (.classEq B (syn_cnc (.cv y))) (.classEq A (syn_cnc (.cv x))) (.classEq (syn_co B (syn_cmuc) A) (syn_co (syn_cnc (.cv y)) (syn_cmuc) (syn_cnc (.cv x)))) p0015
  have p0017 :=
    @g_n_3eqtr4a (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_co (syn_cnc (.cv y)) (syn_cmuc) (syn_cnc (.cv x))) (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A) p0013 p0014 p0016
  have p0018 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) (.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A)) x y dv_cache_0005 dv_cache_0006 p0017
  have p0019 :=
    @g_sylbi (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))))) (.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A)) p0004 p0018
  exact p0019

noncomputable def g_ncdisjun
    (A : Class) (B : Class) (hyp_ncdisjun_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_ncdisjun_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cnc (syn_cun A B)) (syn_cplc (syn_cnc A) (syn_cnc B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let q : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x_ne_r : x ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_r_ne_p : r ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_r : p ≠ r :=
    Ne.symm fresh_r_ne_p
  have fresh_r_ne_q : r ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_q_ne_r : q ≠ r :=
    Ne.symm fresh_r_ne_q
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : r ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_cun A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((Wff.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_A, fresh_r_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_cnc A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_cnc B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0012 : p ∉ ((syn_wbr (.cv x) (syn_cen) (syn_cun A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_not_A, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((syn_wbr (.cv x) (syn_cen) (syn_cun A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_not_A, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : q ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_cnc (syn_cun A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((syn_cplc (syn_cnc A) (syn_cnc B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elnc (.cv x) (syn_cun A B)
  have p0001 :=
    @g_bren (.cv x) (syn_cun A B) r dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_f1ocnv (.cv x) (syn_cun A B) (.cv r)
  have p0003 :=
    @g_imaundi (syn_ccnv (.cv r)) A B
  have p0004 :=
    @g_imadmrn (syn_ccnv (.cv r))
  have p0005 :=
    @g_a1i (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_cdm (syn_ccnv (.cv r)))) (syn_crn (syn_ccnv (.cv r)))) (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) p0004
  have p0006 :=
    @g_f1odm (syn_cun A B) (.cv x) (syn_ccnv (.cv r))
  have p0007 :=
    @g_imaeq2d (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_cdm (syn_ccnv (.cv r))) (syn_cun A B) (syn_ccnv (.cv r)) p0006
  have p0008 :=
    @g_f1ofo (syn_cun A B) (.cv x) (syn_ccnv (.cv r))
  have p0009 :=
    @g_forn (syn_cun A B) (.cv x) (syn_ccnv (.cv r))
  have p0010 :=
    @g_syl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wfo (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (.classEq (syn_crn (syn_ccnv (.cv r))) (.cv x)) p0008 p0009
  have p0011 :=
    @g_n_3eqtr3d (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_cima (syn_ccnv (.cv r)) (syn_cdm (syn_ccnv (.cv r)))) (syn_crn (syn_ccnv (.cv r))) (syn_cima (syn_ccnv (.cv r)) (syn_cun A B)) (.cv x) p0005 p0007 p0010
  have p0012 :=
    @g_syl5eqr (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_cun (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)) (syn_cima (syn_ccnv (.cv r)) (syn_cun A B)) (.cv x) p0003 p0011
  have p0013 :=
    @g_adantl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (.classEq (syn_cun (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)) (.cv x)) (.classEq (syn_cin A B) (syn_c0)) p0012
  have p0014 :=
    @g_f1of1 (syn_cun A B) (.cv x) (syn_ccnv (.cv r))
  have p0015 :=
    @g_ssun1 A B
  have p0016 :=
    @g_f1ores (syn_cun A B) (.cv x) A (syn_ccnv (.cv r))
  have p0017 :=
    @g_sylancl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wss A (syn_cun A B)) (syn_wf1o (syn_cres (syn_ccnv (.cv r)) A) A (syn_cima (syn_ccnv (.cv r)) A)) p0014 p0015 p0016
  have p0018 :=
    @g_f1ocnv A (syn_cima (syn_ccnv (.cv r)) A) (syn_cres (syn_ccnv (.cv r)) A)
  have p0019 :=
    @g_vex r
  have p0020 :=
    @g_cnvex (.cv r) p0019
  have p0021 :=
    @g_resex (syn_ccnv (.cv r)) A p0020 hyp_ncdisjun_1
  have p0022 :=
    @g_cnvex (syn_cres (syn_ccnv (.cv r)) A) p0021
  have p0023 :=
    @g_f1oen (syn_cima (syn_ccnv (.cv r)) A) A (syn_ccnv (syn_cres (syn_ccnv (.cv r)) A)) p0022
  have p0024 :=
    @g_n_3syl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wf1o (syn_cres (syn_ccnv (.cv r)) A) A (syn_cima (syn_ccnv (.cv r)) A)) (syn_wf1o (syn_ccnv (syn_cres (syn_ccnv (.cv r)) A)) (syn_cima (syn_ccnv (.cv r)) A) A) (syn_wbr (syn_cima (syn_ccnv (.cv r)) A) (syn_cen) A) p0017 p0018 p0023
  have p0025 :=
    @g_elnc (syn_cima (syn_ccnv (.cv r)) A) A
  have p0026 :=
    @g_sylibr (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wbr (syn_cima (syn_ccnv (.cv r)) A) (syn_cen) A) (.classMem (syn_cima (syn_ccnv (.cv r)) A) (syn_cnc A)) p0024 p0025
  have p0027 :=
    @g_adantl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (.classMem (syn_cima (syn_ccnv (.cv r)) A) (syn_cnc A)) (.classEq (syn_cin A B) (syn_c0)) p0026
  have p0028 :=
    @g_ssun2 B A
  have p0029 :=
    @g_f1ores (syn_cun A B) (.cv x) B (syn_ccnv (.cv r))
  have p0030 :=
    @g_sylancl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wss B (syn_cun A B)) (syn_wf1o (syn_cres (syn_ccnv (.cv r)) B) B (syn_cima (syn_ccnv (.cv r)) B)) p0014 p0028 p0029
  have p0031 :=
    @g_f1ocnv B (syn_cima (syn_ccnv (.cv r)) B) (syn_cres (syn_ccnv (.cv r)) B)
  have p0032 :=
    @g_resex (syn_ccnv (.cv r)) B p0020 hyp_ncdisjun_2
  have p0033 :=
    @g_cnvex (syn_cres (syn_ccnv (.cv r)) B) p0032
  have p0034 :=
    @g_f1oen (syn_cima (syn_ccnv (.cv r)) B) B (syn_ccnv (syn_cres (syn_ccnv (.cv r)) B)) p0033
  have p0035 :=
    @g_n_3syl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wf1o (syn_cres (syn_ccnv (.cv r)) B) B (syn_cima (syn_ccnv (.cv r)) B)) (syn_wf1o (syn_ccnv (syn_cres (syn_ccnv (.cv r)) B)) (syn_cima (syn_ccnv (.cv r)) B) B) (syn_wbr (syn_cima (syn_ccnv (.cv r)) B) (syn_cen) B) p0030 p0031 p0034
  have p0036 :=
    @g_adantl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wbr (syn_cima (syn_ccnv (.cv r)) B) (syn_cen) B) (.classEq (syn_cin A B) (syn_c0)) p0035
  have p0037 :=
    @g_elnc (syn_cima (syn_ccnv (.cv r)) B) B
  have p0038 :=
    @g_sylibr (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))) (syn_wbr (syn_cima (syn_ccnv (.cv r)) B) (syn_cen) B) (.classMem (syn_cima (syn_ccnv (.cv r)) B) (syn_cnc B)) p0036 p0037
  have p0039 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))))
  have p0040 :=
    @g_simprbi (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wf (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wfun (syn_ccnv (syn_ccnv (.cv r)))) p0039
  have p0041 :=
    @g_imain A B (syn_ccnv (.cv r))
  have p0042 :=
    @g_n_3syl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wfun (syn_ccnv (syn_ccnv (.cv r)))) (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_cin A B)) (syn_cin (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B))) p0014 p0040 p0041
  have p0043 :=
    @g_adantl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_cin A B)) (syn_cin (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B))) (.classEq (syn_cin A B) (syn_c0)) p0042
  have p0044 :=
    @g_imaeq2 (syn_cin A B) (syn_c0) (syn_ccnv (.cv r))
  have p0045 :=
    @g_ima0 (syn_ccnv (.cv r))
  have p0046 :=
    @g_syl6eq (.classEq (syn_cin A B) (syn_c0)) (syn_cima (syn_ccnv (.cv r)) (syn_cin A B)) (syn_cima (syn_ccnv (.cv r)) (syn_c0)) (syn_c0) p0044 p0045
  have p0047 :=
    @g_adantr (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_cin A B)) (syn_c0)) (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) p0046
  have p0048 :=
    @g_eqtr3d (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))) (syn_cima (syn_ccnv (.cv r)) (syn_cin A B)) (syn_cin (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)) (syn_c0) p0043 p0047
  have p0049 :=
    @g_eladdci (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B) (syn_cnc A) (syn_cnc B)
  have p0050 :=
    @g_syl3anc (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))) (.classMem (syn_cima (syn_ccnv (.cv r)) A) (syn_cnc A)) (.classMem (syn_cima (syn_ccnv (.cv r)) B) (syn_cnc B)) (.classEq (syn_cin (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)) (syn_c0)) (.classMem (syn_cun (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)) (syn_cplc (syn_cnc A) (syn_cnc B))) p0027 p0038 p0048 p0049
  have p0051 :=
    @g_eqeltrrd (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))) (syn_cun (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)) (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B)) p0013 p0050
  have p0052 :=
    @g_ex (.classEq (syn_cin A B) (syn_c0)) (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0051
  have p0053 :=
    @g_syl5 (syn_wf1o (.cv r) (.cv x) (syn_cun A B)) (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (.classEq (syn_cin A B) (syn_c0)) (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0002 p0052
  have p0054 :=
    @g_exlimdv (.classEq (syn_cin A B) (syn_c0)) (syn_wf1o (.cv r) (.cv x) (syn_cun A B)) (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) r dv_cache_0003 dv_cache_0004 p0053
  have p0055 :=
    @g_syl5bi (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) (syn_wex r (syn_wf1o (.cv r) (.cv x) (syn_cun A B))) (.classEq (syn_cin A B) (syn_c0)) (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0001 p0054
  have p0056 :=
    @g_eladdc (.cv x) (syn_cnc A) (syn_cnc B) p q dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0057 :=
    @g_simplrl (.classEq (syn_cin A B) (syn_c0)) (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
  have p0058 :=
    @g_elnc (.cv p) A
  have p0059 :=
    @g_sylib (syn_wa (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))) (.classMem (.cv p) (syn_cnc A)) (syn_wbr (.cv p) (syn_cen) A) p0057 p0058
  have p0060 :=
    @g_simplrr (.classEq (syn_cin A B) (syn_c0)) (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
  have p0061 :=
    @g_elnc (.cv q) B
  have p0062 :=
    @g_sylib (syn_wa (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))) (.classMem (.cv q) (syn_cnc B)) (syn_wbr (.cv q) (syn_cen) B) p0060 p0061
  have p0063 :=
    @g_simpr (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
  have p0064 :=
    @g_simpll (.classEq (syn_cin A B) (syn_c0)) (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
  have p0065 :=
    @g_unen (.cv p) A (.cv q) B
  have p0066 :=
    @g_syl22anc (syn_wa (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))) (syn_wbr (.cv p) (syn_cen) A) (syn_wbr (.cv q) (syn_cen) B) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0)) (.classEq (syn_cin A B) (syn_c0)) (syn_wbr (syn_cun (.cv p) (.cv q)) (syn_cen) (syn_cun A B)) p0059 p0062 p0063 p0064 p0065
  have p0067 :=
    @g_breq1 (.cv x) (syn_cun (.cv p) (.cv q)) (syn_cun A B) (syn_cen)
  have p0068 :=
    @g_syl5ibrcom (syn_wa (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))) (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) (.classEq (.cv x) (syn_cun (.cv p) (.cv q))) (syn_wbr (syn_cun (.cv p) (.cv q)) (syn_cen) (syn_cun A B)) p0066 p0067
  have p0069 :=
    @g_expimpd (syn_wa (.classEq (syn_cin A B) (syn_c0)) (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv p) (.cv q))) (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) p0068
  have p0070 :=
    @g_rexlimdvva (.classEq (syn_cin A B) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv p) (.cv q)))) (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) p q (syn_cnc A) (syn_cnc B) dv_cache_0008 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0011 p0069
  have p0071 :=
    @g_syl5bi (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) (syn_wrex p (syn_cnc A) (syn_wrex q (syn_cnc B) (syn_wa (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv p) (.cv q)))))) (.classEq (syn_cin A B) (syn_c0)) (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) p0056 p0070
  have p0072 :=
    @g_impbid (.classEq (syn_cin A B) (syn_c0)) (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0055 p0071
  have p0073 :=
    @g_syl5bb (.classMem (.cv x) (syn_cnc (syn_cun A B))) (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) (.classEq (syn_cin A B) (syn_c0)) (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0000 p0072
  have p0074 :=
    @g_eqrdv (.classEq (syn_cin A B) (syn_c0)) x (syn_cnc (syn_cun A B)) (syn_cplc (syn_cnc A) (syn_cnc B)) dv_cache_0016 dv_cache_0017 dv_cache_0018 p0073
  exact p0074

#print axioms g_ncdisjun

end NFChoice.DirectNominalPrf.WPPReplay
