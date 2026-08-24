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
import NominalWPPReplayChunk013Compact001Part020

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

noncomputable def g_connexex
     :
    Nominal.NPrf (.classMem (syn_cconnex) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let p : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_r : x ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_y_ne_r : y ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_p : y ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_r_ne_a : r ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    Ne.symm fresh_r_ne_a
  have fresh_r_ne_p : r ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_p_ne_r : p ≠ r :=
    Ne.symm fresh_r_ne_p
  have fresh_a_ne_p : a ≠ p := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have dv_cache_0001 : a ≠ r := by
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0004 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0005 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ∉ ((syn_cop (.cv r) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_r, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : p ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((syn_cop (.cv y) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : r ∉ ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : a ∉ ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_connex x y r a dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_vex r
  have p0002 :=
    @g_vex a
  have p0003 :=
    @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c)) p0003
  have p0005 :=
    @g_elima1c x (syn_cop (.cv r) (.cv a)) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) dv_cache_0007 dv_cache_0008
  have p0006 :=
    @g_elin (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))
  have p0007 :=
    @g_otelins2 (syn_csn (.cv x)) (.cv r) (.cv a) (syn_csset) p0001
  have p0008 :=
    @g_vex x
  have p0009 :=
    @g_opelssetsn (.cv x) (.cv a) p0008 p0002
  have p0010_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a) p0007 p0010_e01_recanon
  have p0011 :=
    @g_elima1c y (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) dv_cache_0009 dv_cache_0010
  have p0012 :=
    @g_eldif (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
  have p0013 :=
    @g_snex (.cv x)
  have p0014 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)) (syn_cins2 (syn_csset)) p0013
  have p0015 :=
    @g_otelins2 (syn_csn (.cv y)) (.cv r) (.cv a) (syn_csset) p0001
  have p0016 :=
    @g_vex y
  have p0017 :=
    @g_opelssetsn (.cv y) (.cv a) p0016 p0002
  have p0018_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0017
  have p0018 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a) p0014 p0015 p0018_e02_recanon
  have p0019 :=
    @g_oqelins4 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (.cv a) (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) p0002
  have p0020 :=
    @g_elun (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))
  have p0021 :=
    @g_elin (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0022 :=
    @g_oqelins4 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (syn_csi3 (syn_cswap)) p0001
  have p0023 :=
    @g_vex p
  have p0024 :=
    @g_otsnelsi3 (.cv p) (.cv y) (.cv x) (syn_cswap) p0023 p0016 p0008
  have p0025 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cswap) (syn_cop (.cv y) (.cv x)))))
  have p0026 :=
    @g_brswap2 (.cv p) (.cv y) (.cv x) p0016 p0008
  have p0027 :=
    @g_bitr3i (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cswap)) (syn_wbr (.cv p) (syn_cswap) (syn_cop (.cv y) (.cv x))) (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0025 p0026
  have p0028 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cswap)))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_csi3 (syn_cswap))) (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cswap)) (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0022 p0024 p0027
  have p0029 :=
    @g_snex (.cv y)
  have p0030 :=
    @g_otelins2 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_cins2 (syn_csset)) p0029
  have p0031 :=
    @g_otelins2 (syn_csn (.cv p)) (syn_csn (.cv x)) (.cv r) (syn_csset) p0013
  have p0032 :=
    @g_opelssetsn (.cv p) (.cv r) p0023 p0001
  have p0033_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0032
  have p0033 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r) p0030 p0031 p0033_e02_recanon
  have p0034 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cswap)))) (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem p r) p0028 p0033
  have p0035 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cswap)))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)) p0021 p0034
  have p0036 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)) p p0035
  have p0037 :=
    @g_elima1c p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) dv_cache_0011 dv_cache_0012
  have p0038 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv y))))
  have p0039 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p (syn_cop (.cv x) (.cv y)) (.cv r) dv_cache_0013 dv_cache_0014))
  have p0040_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0039
  have p0040 :=
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r))) p0038 p0040_e01_recanon
  have p0041 :=
    @g_n_3bitr4i (syn_wex p (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv x) (.cv r) (.cv y)) p0036 p0037 p0040
  have p0042 :=
    @g_elin (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0043 :=
    @g_oqelins4 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (syn_csi3 (syn_cid)) p0001
  have p0044 :=
    @g_otsnelsi3 (.cv p) (.cv y) (.cv x) (syn_cid) p0023 p0016 p0008
  have p0045 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cid) (syn_cop (.cv y) (.cv x)))))
  have p0046 :=
    @g_opex (.cv y) (.cv x) p0016 p0008
  have p0047 :=
    @g_ideq (.cv p) (syn_cop (.cv y) (.cv x)) p0046
  have p0048 :=
    @g_bitr3i (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cid)) (syn_wbr (.cv p) (syn_cid) (syn_cop (.cv y) (.cv x))) (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) p0045 p0047
  have p0049 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_csi3 (syn_cid))) (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cid)) (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) p0043 p0044 p0048
  have p0050 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem p r) p0049 p0033
  have p0051 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)) p0042 p0050
  have p0052 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)) p p0051
  have p0053 :=
    @g_elima1c p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) dv_cache_0011 dv_cache_0015
  have p0054 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv x))))
  have p0055 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p (syn_cop (.cv y) (.cv x)) (.cv r) dv_cache_0016 dv_cache_0014))
  have p0056_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0055
  have p0056 :=
    @g_bitri (syn_wbr (.cv y) (.cv r) (.cv x)) (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r))) p0054 p0056_e01_recanon
  have p0057 :=
    @g_n_3bitr4i (syn_wex p (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv y) (.cv r) (.cv x)) p0052 p0053 p0056
  have p0058 :=
    @g_orbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv x) (.cv r) (.cv y)) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv y) (.cv r) (.cv x)) p0041 p0057
  have p0059 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_wo (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) p0019 p0020 p0058
  have p0060 :=
    @g_notbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) p0059
  have p0061 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem y a) (.neg (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))) p0018 p0060
  have p0062 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.neg (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))) (syn_wa (.objMem y a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) p0012 p0061
  have p0063 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_wa (.objMem y a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) y p0062
  have p0064 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_wex y (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))) (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))) p0011 p0063
  have p0065 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (.cv a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))))
  have p0066 :=
    @g_rexnal (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) y (.cv a)
  have p0067_e01_recanon : Nominal.NPrf (syn_wb (syn_wrex y (.cv a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_wo syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0065
  have p0067 :=
    @g_n_3bitr2i (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))) (syn_wrex y (.cv a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) p0064 p0067_e01_recanon p0066
  have p0068 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.objMem x a) (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) p0010 p0067
  have p0069 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))) (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))) p0006 p0068
  have p0070 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))) (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))) x p0069
  have p0071 :=
    @g_bitri (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c))) (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))))) p0005 p0070
  have p0072 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))))))
  have p0073 :=
    @g_rexnal (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))) x (.cv a)
  have p0074_e01_recanon : Nominal.NPrf (syn_wb (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_wral syn_wo syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0072
  have p0074 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))))) (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))) (.neg (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))) p0071 p0074_e01_recanon p0073
  have p0075 :=
    @g_con2bii (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c))) (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) p0074
  have p0076 :=
    @g_bitr4i (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c)))) (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c)))) (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) p0004 p0075
  have p0077 :=
    @g_opabbi2i (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) r a (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c))) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0076
  have p0078 :=
    @g_eqtr4i (syn_cconnex) (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c))) p0000 p0077
  have p0079 :=
    @g_ssetex
  have p0080 :=
    @g_ins2ex (syn_csset) p0079
  have p0081 :=
    @g_ins2ex (syn_cins2 (syn_csset)) p0080
  have p0082 :=
    @g_swapex
  have p0083 :=
    @g_si3ex (syn_cswap) p0082
  have p0084 :=
    @g_ins4ex (syn_csi3 (syn_cswap)) p0083
  have p0085 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))) p0084 p0081
  have p0086 :=
    @g_n_1cex
  have p0087 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c) p0085 p0086
  have p0088 :=
    @g_idex
  have p0089 :=
    @g_si3ex (syn_cid) p0088
  have p0090 :=
    @g_ins4ex (syn_csi3 (syn_cid)) p0089
  have p0091 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))) p0090 p0081
  have p0092 :=
    @g_n_1cex
  have p0093 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c) p0091 p0092
  have p0094 :=
    @g_unex (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) p0087 p0093
  have p0095 :=
    @g_ins4ex (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) p0094
  have p0096 :=
    @g_difex (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) p0081 p0095
  have p0097 :=
    @g_n_1cex
  have p0098 :=
    @g_imaex (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c) p0096 p0097
  have p0099 :=
    @g_inex (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)) p0080 p0098
  have p0100 :=
    @g_n_1cex
  have p0101 :=
    @g_imaex (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c) p0099 p0100
  have p0102 :=
    @g_complex (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c)) p0101
  have p0103 :=
    @g_eqeltri (syn_cconnex) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c))) (syn_cvv) p0078 p0102
  exact p0103

#print axioms g_connexex

end NFChoice.DirectNominalPrf.WPPReplay
