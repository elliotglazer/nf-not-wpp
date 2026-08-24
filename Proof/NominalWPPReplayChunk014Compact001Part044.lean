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
import NominalWPPReplayChunk014Compact001Part043

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

noncomputable def g_werestrndv
    (ph : Wff) (B : Class) (D : Class) (S : Class) (hyp_werestrndv_1 : Nominal.NPrf (.imp ph (syn_wbr S (syn_cwe) D))) (hyp_werestrndv_2 : Nominal.NPrf (.imp ph (syn_wss B D))) (hyp_werestrndv_3 : Nominal.NPrf (.imp ph (.classMem B (syn_cvv)))) :
    Nominal.NPrf (.imp ph (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cwe) B)) := by
  let proofSupport : Finset Var := ph.fv ∪ B.fv ∪ D.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_S : z ∉ S.fv := by
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
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cin S (syn_cxp B B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cin S (syn_cxp B B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_S, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cin S (syn_cxp B B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_S, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0013 : z ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0018 : y ∉ ((syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_ph, fresh_y_ne_x, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex S D (syn_cwe)
  have p0001 :=
    @g_simpld (syn_wbr S (syn_cwe) D) (.classMem S (syn_cvv)) (.classMem D (syn_cvv)) p0000
  have p0002 :=
    @g_syl ph (syn_wbr S (syn_cwe) D) (.classMem S (syn_cvv)) hyp_werestrndv_1 p0001
  have p0003 :=
    @g_jca ph (.classMem B (syn_cvv)) (.classMem B (syn_cvv)) hyp_werestrndv_3 hyp_werestrndv_3
  have p0004 :=
    @g_xpexg B B (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl ph (syn_wa (.classMem B (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_cxp B B) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca ph (.classMem S (syn_cvv)) (.classMem (syn_cxp B B) (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_inexg S (syn_cxp B B) (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl ph (syn_wa (.classMem S (syn_cvv)) (.classMem (syn_cxp B B) (syn_cvv))) (.classMem (syn_cin S (syn_cxp B B)) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_simpl ph (.classMem (.cv x) B)
  have p0010 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0011 :=
    @g_breqi S D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0010
  have p0012 :=
    @g_brin S D (syn_cstrict) (syn_cfound)
  have p0013 :=
    @g_bitri (syn_wbr S (syn_cwe) D) (syn_wbr S (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0011 p0012
  have p0014 :=
    @g_biimpi (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0013
  have p0015 :=
    @g_syl ph (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) hyp_werestrndv_1 p0014
  have p0016 :=
    @g_simpld ph (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D) p0015
  have p0017 :=
    @g_sopc D S
  have p0018 :=
    @g_sylib ph (syn_wbr S (syn_cstrict) D) (syn_wa (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D)) p0016 p0017
  have p0019 :=
    @g_simpld ph (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D) p0018
  have p0020 :=
    @g_porta D S
  have p0021 :=
    @g_sylib ph (syn_wbr S (syn_cpartial) D) (syn_w3a (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D) (syn_wbr S (syn_cantisym) D)) p0019 p0020
  have p0022 :=
    @g_simp1d ph (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D) (syn_wbr S (syn_cantisym) D) p0021
  have p0023 :=
    @g_syl (syn_wa ph (.classMem (.cv x) B)) ph (syn_wbr S (syn_cref) D) p0009 p0022
  have p0024 :=
    @g_sselda ph B D (.cv x) hyp_werestrndv_2
  have p0025 :=
    @g_refd (syn_wa ph (.classMem (.cv x) B)) D S (.cv x) p0023 p0024
  have p0026 :=
    @g_simpr ph (.classMem (.cv x) B)
  have p0027 :=
    @g_simpr ph (.classMem (.cv x) B)
  have p0028 :=
    @g_jca (syn_wa ph (.classMem (.cv x) B)) (.classMem (.cv x) B) (.classMem (.cv x) B) p0026 p0027
  have p0029 :=
    @g_brinxp (.cv x) (.cv x) B B S
  have p0030 :=
    @g_syl (syn_wa ph (.classMem (.cv x) B)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) B)) (syn_wb (syn_wbr (.cv x) S (.cv x)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv x))) p0028 p0029
  have p0031 :=
    @g_mpbid (syn_wa ph (.classMem (.cv x) B)) (syn_wbr (.cv x) S (.cv x)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv x)) p0025 p0030
  have p0032 :=
    @g_simp1 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0033 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0034 :=
    @g_breqi S D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0033
  have p0035 :=
    @g_brin S D (syn_cstrict) (syn_cfound)
  have p0036 :=
    @g_bitri (syn_wbr S (syn_cwe) D) (syn_wbr S (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0034 p0035
  have p0037 :=
    @g_biimpi (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0036
  have p0038 :=
    @g_syl ph (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) hyp_werestrndv_1 p0037
  have p0039 :=
    @g_simpld ph (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D) p0038
  have p0040 :=
    @g_sopc D S
  have p0041 :=
    @g_sylib ph (syn_wbr S (syn_cstrict) D) (syn_wa (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D)) p0039 p0040
  have p0042 :=
    @g_simpld ph (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D) p0041
  have p0043 :=
    @g_porta D S
  have p0044 :=
    @g_sylib ph (syn_wbr S (syn_cpartial) D) (syn_w3a (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D) (syn_wbr S (syn_cantisym) D)) p0042 p0043
  have p0045 :=
    @g_simp2d ph (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D) (syn_wbr S (syn_cantisym) D) p0044
  have p0046 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) ph (syn_wbr S (syn_ctrans) D) p0032 p0045
  have p0047 :=
    @g_simp1 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0048 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) ph (syn_wss B D) p0047 hyp_werestrndv_2
  have p0049 :=
    @g_simp2 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0050 :=
    @g_simp1 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0051 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (.classMem (.cv x) B) p0049 p0050
  have p0052 :=
    @g_sseldd (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) B D (.cv x) p0048 p0051
  have p0053 :=
    @g_simp1 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0054 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) ph (syn_wss B D) p0053 hyp_werestrndv_2
  have p0055 :=
    @g_simp2 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0056 :=
    @g_simp2 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0057 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (.classMem (.cv y) B) p0055 p0056
  have p0058 :=
    @g_sseldd (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) B D (.cv y) p0054 p0057
  have p0059 :=
    @g_simp1 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0060 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) ph (syn_wss B D) p0059 hyp_werestrndv_2
  have p0061 :=
    @g_simp2 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0062 :=
    @g_simp3 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0063 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (.classMem (.cv z) B) p0061 p0062
  have p0064 :=
    @g_sseldd (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) B D (.cv z) p0060 p0063
  have p0065 :=
    @g_simp3 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0066 :=
    @g_simpld (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) p0065
  have p0067 :=
    @g_brin (.cv x) (.cv y) S (syn_cxp B B)
  have p0068 :=
    @g_simplbi (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cxp B B) (.cv y)) p0067
  have p0069 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv x) S (.cv y)) p0066 p0068
  have p0070 :=
    @g_simp3 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0071 :=
    @g_simprd (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) p0070
  have p0072 :=
    @g_brin (.cv y) (.cv z) S (syn_cxp B B)
  have p0073 :=
    @g_simplbi (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (syn_wbr (.cv y) S (.cv z)) (syn_wbr (.cv y) (syn_cxp B B) (.cv z)) p0072
  have p0074 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (syn_wbr (.cv y) S (.cv z)) p0071 p0073
  have p0075 :=
    @g_trd (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) D S (.cv x) (.cv y) (.cv z) p0046 p0052 p0058 p0064 p0069 p0074
  have p0076 :=
    @g_simp2 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0077 :=
    @g_simp1 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0078 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (.classMem (.cv x) B) p0076 p0077
  have p0079 :=
    @g_simp2 ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0080 :=
    @g_simp3 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0081 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (.classMem (.cv z) B) p0079 p0080
  have p0082 :=
    @g_jca (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (.classMem (.cv x) B) (.classMem (.cv z) B) p0078 p0081
  have p0083 :=
    @g_brinxp (.cv x) (.cv z) B B S
  have p0084 :=
    @g_syl (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv z) B)) (syn_wb (syn_wbr (.cv x) S (.cv z)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv z))) p0082 p0083
  have p0085 :=
    @g_mpbid (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))) (syn_wbr (.cv x) S (.cv z)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv z)) p0075 p0084
  have p0086 :=
    @g_simp1 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0087 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0088 :=
    @g_breqi S D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0087
  have p0089 :=
    @g_brin S D (syn_cstrict) (syn_cfound)
  have p0090 :=
    @g_bitri (syn_wbr S (syn_cwe) D) (syn_wbr S (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0088 p0089
  have p0091 :=
    @g_biimpi (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0090
  have p0092 :=
    @g_syl ph (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) hyp_werestrndv_1 p0091
  have p0093 :=
    @g_simpld ph (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D) p0092
  have p0094 :=
    @g_sopc D S
  have p0095 :=
    @g_sylib ph (syn_wbr S (syn_cstrict) D) (syn_wa (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D)) p0093 p0094
  have p0096 :=
    @g_simpld ph (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D) p0095
  have p0097 :=
    @g_porta D S
  have p0098 :=
    @g_sylib ph (syn_wbr S (syn_cpartial) D) (syn_w3a (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D) (syn_wbr S (syn_cantisym) D)) p0096 p0097
  have p0099 :=
    @g_simp3d ph (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D) (syn_wbr S (syn_cantisym) D) p0098
  have p0100 :=
    @g_syl (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) ph (syn_wbr S (syn_cantisym) D) p0086 p0099
  have p0101 :=
    @g_simp1 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0102 :=
    @g_syl (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) ph (syn_wss B D) p0101 hyp_werestrndv_2
  have p0103 :=
    @g_simp2 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0104 :=
    @g_simpld (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) (.classMem (.cv x) B) (.classMem (.cv y) B) p0103
  have p0105 :=
    @g_sseldd (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) B D (.cv x) p0102 p0104
  have p0106 :=
    @g_simp1 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0107 :=
    @g_syl (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) ph (syn_wss B D) p0106 hyp_werestrndv_2
  have p0108 :=
    @g_simp2 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0109 :=
    @g_simprd (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) (.classMem (.cv x) B) (.classMem (.cv y) B) p0108
  have p0110 :=
    @g_sseldd (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) B D (.cv y) p0107 p0109
  have p0111 :=
    @g_simp3 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0112 :=
    @g_simpld (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)) p0111
  have p0113 :=
    @g_brin (.cv x) (.cv y) S (syn_cxp B B)
  have p0114 :=
    @g_simplbi (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cxp B B) (.cv y)) p0113
  have p0115 :=
    @g_syl (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv x) S (.cv y)) p0112 p0114
  have p0116 :=
    @g_simp3 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0117 :=
    @g_simprd (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)) p0116
  have p0118 :=
    @g_brin (.cv y) (.cv x) S (syn_cxp B B)
  have p0119 :=
    @g_simplbi (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)) (syn_wbr (.cv y) S (.cv x)) (syn_wbr (.cv y) (syn_cxp B B) (.cv x)) p0118
  have p0120 :=
    @g_syl (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)) (syn_wbr (.cv y) S (.cv x)) p0117 p0119
  have p0121 :=
    @g_antid (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) D S (.cv x) (.cv y) p0100 p0105 p0110 p0115 p0120
  have p0122 :=
    @g_simp1 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0123 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0124 :=
    @g_breqi S D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0123
  have p0125 :=
    @g_brin S D (syn_cstrict) (syn_cfound)
  have p0126 :=
    @g_bitri (syn_wbr S (syn_cwe) D) (syn_wbr S (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0124 p0125
  have p0127 :=
    @g_biimpi (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0126
  have p0128 :=
    @g_syl ph (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) hyp_werestrndv_1 p0127
  have p0129 :=
    @g_simpld ph (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D) p0128
  have p0130 :=
    @g_sopc D S
  have p0131 :=
    @g_sylib ph (syn_wbr S (syn_cstrict) D) (syn_wa (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D)) p0129 p0130
  have p0132 :=
    @g_simprd ph (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D) p0131
  have p0133 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph (syn_wbr S (syn_cconnex) D) p0122 p0132
  have p0134 :=
    @g_simp1 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0135 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph (syn_wss B D) p0134 hyp_werestrndv_2
  have p0136 :=
    @g_simp2 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0137 :=
    @g_sseldd (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B D (.cv x) p0135 p0136
  have p0138 :=
    @g_simp1 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0139 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph (syn_wss B D) p0138 hyp_werestrndv_2
  have p0140 :=
    @g_simp3 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0141 :=
    @g_sseldd (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B D (.cv y) p0139 p0140
  have p0142 :=
    @g_connexd (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) D S (.cv x) (.cv y) p0133 p0137 p0141
  have p0143 :=
    @g_simp2 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0144 :=
    @g_simp3 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0145 :=
    @g_jca (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv x) B) (.classMem (.cv y) B) p0143 p0144
  have p0146 :=
    @g_brinxp (.cv x) (.cv y) B B S
  have p0147 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))) p0145 p0146
  have p0148 :=
    @g_simp3 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0149 :=
    @g_simp2 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0150 :=
    @g_jca (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv y) B) (.classMem (.cv x) B) p0148 p0149
  have p0151 :=
    @g_brinxp (.cv y) (.cv x) B B S
  have p0152 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) B)) (syn_wb (syn_wbr (.cv y) S (.cv x)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))) p0150 p0151
  have p0153 :=
    @g_orbi12d (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) S (.cv x)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)) p0147 p0152
  have p0154 :=
    @g_mpbid (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wo (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv y) S (.cv x))) (syn_wo (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))) p0142 p0153
  have p0155_e04_recanon : Nominal.NPrf (.imp (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0121
  have p0155 :=
    @g_sod ph x y z B (syn_cin S (syn_cxp B B)) (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0008 hyp_werestrndv_3 p0031 p0085 p0155_e04_recanon p0154
  have p0156 :=
    @g_brex S D (syn_cwe)
  have p0157 :=
    @g_simpld (syn_wbr S (syn_cwe) D) (.classMem S (syn_cvv)) (.classMem D (syn_cvv)) p0156
  have p0158 :=
    @g_syl ph (syn_wbr S (syn_cwe) D) (.classMem S (syn_cvv)) hyp_werestrndv_1 p0157
  have p0159 :=
    @g_jca ph (.classMem B (syn_cvv)) (.classMem B (syn_cvv)) hyp_werestrndv_3 hyp_werestrndv_3
  have p0160 :=
    @g_xpexg B B (syn_cvv) (syn_cvv)
  have p0161 :=
    @g_syl ph (syn_wa (.classMem B (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_cxp B B) (syn_cvv)) p0159 p0160
  have p0162 :=
    @g_jca ph (.classMem S (syn_cvv)) (.classMem (syn_cxp B B) (syn_cvv)) p0158 p0161
  have p0163 :=
    @g_inexg S (syn_cxp B B) (syn_cvv) (syn_cvv)
  have p0164 :=
    @g_syl ph (syn_wa (.classMem S (syn_cvv)) (.classMem (syn_cxp B B) (syn_cvv))) (.classMem (syn_cin S (syn_cxp B B)) (syn_cvv)) p0162 p0163
  have p0165 :=
    @g_simpl ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0166 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0167 :=
    @g_breqi S D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0166
  have p0168 :=
    @g_brin S D (syn_cstrict) (syn_cfound)
  have p0169 :=
    @g_bitri (syn_wbr S (syn_cwe) D) (syn_wbr S (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0167 p0168
  have p0170 :=
    @g_biimpi (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0169
  have p0171 :=
    @g_syl ph (syn_wbr S (syn_cwe) D) (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) hyp_werestrndv_1 p0170
  have p0172 :=
    @g_simprd ph (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D) p0171
  have p0173 :=
    @g_syl (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) ph (syn_wbr S (syn_cfound) D) p0165 p0172
  have p0174 :=
    @g_vex x
  have p0175 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) p0174
  have p0176 :=
    @g_simpr ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0177 :=
    @g_simpld (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)) p0176
  have p0178 :=
    @g_simpl ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0179 :=
    @g_syl (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) ph (syn_wss B D) p0178 hyp_werestrndv_2
  have p0180 :=
    @g_sstrd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (.cv x) B D p0177 p0179
  have p0181 :=
    @g_simpr ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0182 :=
    @g_simprd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)) p0181
  have p0183 :=
    @g_frd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) z y D S (syn_cvv) (.cv x) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 p0173 p0175 p0180 p0182
  have p0184 :=
    @g_brin (.cv y) (.cv z) S (syn_cxp B B)
  have p0185 :=
    @g_simplbi (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (syn_wbr (.cv y) S (.cv z)) (syn_wbr (.cv y) (syn_cxp B B) (.cv z)) p0184
  have p0186 :=
    @g_imim1i (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)) p0185
  have p0187 :=
    @g_a1i (.imp (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))) (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (.classEq (.cv y) (.cv z)))) (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) p0186
  have p0188 :=
    @g_ralimdv (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))) (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (.classEq (.cv y) (.cv z))) y (.cv x) dv_cache_0018 p0187
  have p0189 :=
    @g_reximdv (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (.classEq (.cv y) (.cv z)))) z (.cv x) dv_cache_0019 p0188
  have p0190_e00_recanon : Nominal.NPrf (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
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
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0183
  have p0190 :=
    @g_mpd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (.classEq (.cv y) (.cv z))))) p0190_e00_recanon p0189
  have p0191_e02_recanon : Nominal.NPrf (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_cin syn_cxp syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0190
  have p0191 :=
    @g_frrd ph x y z B (syn_cin S (syn_cxp B B)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0164 hyp_werestrndv_3 p0191_e02_recanon
  have p0192 :=
    @g_jca ph (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cstrict) B) (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cfound) B) p0155 p0191
  have p0193 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0194 :=
    @g_breqi (syn_cin S (syn_cxp B B)) B (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0193
  have p0195 :=
    @g_brin (syn_cin S (syn_cxp B B)) B (syn_cstrict) (syn_cfound)
  have p0196 :=
    @g_bitri (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cwe) B) (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cin (syn_cstrict) (syn_cfound)) B) (syn_wa (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cstrict) B) (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cfound) B)) p0194 p0195
  have p0197 :=
    @g_a1i (syn_wb (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cwe) B) (syn_wa (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cstrict) B) (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cfound) B))) ph p0196
  have p0198 :=
    @g_mpbird ph (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cwe) B) (syn_wa (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cstrict) B) (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cfound) B)) p0192 p0197
  exact p0198

noncomputable def g_westrseg
    (x : Var) (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0001 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0002 :=
    @g_a1i (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0001
  have p0003 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0004 :=
    @g_brex R D (syn_cwe)
  have p0005 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0003 p0004
  have p0006 :=
    @g_simprd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0005
  have p0007 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0008 :=
    @g_brex R D (syn_cwe)
  have p0009 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0007 p0008
  have p0010 :=
    @g_simpld (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0009
  have p0011 :=
    @g_idex
  have p0012 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0011
  have p0013 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0017 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0015 p0016
  have p0018 :=
    @g_snex (.cv x)
  have p0019 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0018
  have p0020 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0017 p0019
  have p0021 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0022 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0006 p0022
  have p0024 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_werestr (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R dv_cache_0001 p0000 p0002 p0025
  exact p0026

noncomputable def g_westrsegndv
    (x : Var) (D : Class) (S : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr (syn_cin S (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ S.fv
  have p0000 :=
    @g_simpl (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)
  have p0001 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))
  have p0002 :=
    @g_a1i (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) D) (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) p0001
  have p0003 :=
    @g_simpl (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)
  have p0004 :=
    @g_brex S D (syn_cwe)
  have p0005 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr S (syn_cwe) D) (syn_wa (.classMem S (syn_cvv)) (.classMem D (syn_cvv))) p0003 p0004
  have p0006 :=
    @g_simprd (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (.classMem S (syn_cvv)) (.classMem D (syn_cvv)) p0005
  have p0007 :=
    @g_simpl (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)
  have p0008 :=
    @g_brex S D (syn_cwe)
  have p0009 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr S (syn_cwe) D) (syn_wa (.classMem S (syn_cvv)) (.classMem D (syn_cvv))) p0007 p0008
  have p0010 :=
    @g_simpld (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (.classMem S (syn_cvv)) (.classMem D (syn_cvv)) p0009
  have p0011 :=
    @g_idex
  have p0012 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv)) (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) p0011
  have p0013 :=
    @g_jca (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (.classMem S (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_difexg S (syn_cid) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem S (syn_cvv)) (.classMem (syn_cid) (syn_cvv))) (.classMem (syn_cdif S (syn_cid)) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_cnvexg (syn_cdif S (syn_cid)) (syn_cvv)
  have p0017 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (syn_cdif S (syn_cid)) (syn_cvv)) (.classMem (syn_ccnv (syn_cdif S (syn_cid))) (syn_cvv)) p0015 p0016
  have p0018 :=
    @g_snex (.cv x)
  have p0019 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv)) (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) p0018
  have p0020 :=
    @g_jca (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (syn_ccnv (syn_cdif S (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0017 p0019
  have p0021 :=
    @g_imaexg (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0022 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (syn_ccnv (syn_cdif S (syn_cid))) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv))) (.classMem (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_jca (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cvv)) p0006 p0022
  have p0024 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cvv))) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_werestrndv (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) D S p0000 p0002 p0025
  exact p0026

noncomputable def g_strictsegnel
    (x : Var) (D : Class) (R : Class) :
    Nominal.NPrf (.neg (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_eqid (.cv x)
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_ideq (.cv x) (.cv x) p0001
  have p0003 :=
    @g_mpbir (syn_wbr (.cv x) (syn_cid) (.cv x)) (.classEq (.cv x) (.cv x)) p0000 p0002
  have p0004 :=
    @g_notnoti (syn_wbr (.cv x) (syn_cid) (.cv x)) p0003
  have p0005 :=
    @g_intnan (.neg (syn_wbr (.cv x) (syn_cid) (.cv x))) (syn_wbr (.cv x) R (.cv x)) p0004
  have p0006 :=
    @g_brdif (.cv x) (.cv x) R (syn_cid)
  have p0007 :=
    @g_mtbir (syn_wbr (.cv x) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (.cv x) R (.cv x)) (.neg (syn_wbr (.cv x) (syn_cid) (.cv x)))) p0005 p0006
  have p0008 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv x)
  have p0009 :=
    @g_mtbir (.classMem (.cv x) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (.cv x) (syn_cdif R (syn_cid)) (.cv x)) p0007 p0008
  have p0010 :=
    @g_intnan (.classMem (.cv x) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.classMem (.cv x) D) p0009
  have p0011 :=
    @g_elin (.cv x) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0012 :=
    @g_mtbir (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv x) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0010 p0011
  exact p0012

#print axioms g_strictsegnel

end NFChoice.DirectNominalPrf.WPPReplay
