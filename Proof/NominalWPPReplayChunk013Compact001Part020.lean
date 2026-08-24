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
import NominalWPPReplayChunk013Compact001Part019

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

noncomputable def g_antisymex
     :
    Nominal.NPrf (.classMem (syn_cantisym) (syn_cvv)) := by
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
  have dv_cache_0007 : p ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_cop (.cv y) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_r, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cop (.cv r) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : r ∉ ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : a ∉ ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_antisym x y r a dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_vex r
  have p0002 :=
    @g_vex a
  have p0003 :=
    @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)) p0003
  have p0005 :=
    @g_elin (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))
  have p0006 :=
    @g_otelins2 (syn_csn (.cv x)) (.cv r) (.cv a) (syn_csset) p0001
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_opelssetsn (.cv x) (.cv a) p0007 p0002
  have p0009_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a)) :=
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
      p0008
  have p0009 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a) p0006 p0009_e01_recanon
  have p0010 :=
    @g_elin (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))
  have p0011 :=
    @g_snex (.cv x)
  have p0012 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)) (syn_cins2 (syn_csset)) p0011
  have p0013 :=
    @g_otelins2 (syn_csn (.cv y)) (.cv r) (.cv a) (syn_csset) p0001
  have p0014 :=
    @g_vex y
  have p0015 :=
    @g_opelssetsn (.cv y) (.cv a) p0014 p0002
  have p0016_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a)) :=
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
      p0015
  have p0016 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a) p0012 p0013 p0016_e02_recanon
  have p0017 :=
    @g_oqelins4 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (.cv a) (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))) p0002
  have p0018 :=
    @g_eldif (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))
  have p0019 :=
    @g_elin (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))
  have p0020 :=
    @g_elin (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0021 :=
    @g_oqelins4 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0001
  have p0022 :=
    @g_vex p
  have p0023 :=
    @g_otsnelsi3 (.cv p) (.cv y) (.cv x) (syn_ctxp (syn_c2nd) (syn_c1st)) p0022 p0014 p0007
  have p0024 :=
    @g_oteltxp (.cv p) (.cv y) (.cv x) (syn_c2nd) (syn_c1st)
  have p0025 :=
    @g_ancom (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st))
  have p0026 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c1st) (.cv x))))
  have p0027 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c2nd) (.cv y))))
  have p0028 :=
    @g_anbi12i (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st)) (syn_wbr (.cv p) (syn_c2nd) (.cv y)) (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd)) p0026 p0027
  have p0029 :=
    @g_bitr4i (syn_wa (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st))) (syn_wa (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st)) (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv p) (syn_c2nd) (.cv y))) p0025 p0028
  have p0030 :=
    @g_op1st2nd (.cv x) (.cv y) (.cv p) p0007 p0014
  have p0031 :=
    @g_n_3bitri (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st))) (syn_wa (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv p) (syn_c2nd) (.cv y))) (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0024 p0029 p0030
  have p0032 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st))) (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0021 p0023 p0031
  have p0033 :=
    @g_snex (.cv y)
  have p0034 :=
    @g_otelins2 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_cins2 (syn_csset)) p0033
  have p0035 :=
    @g_otelins2 (syn_csn (.cv p)) (syn_csn (.cv x)) (.cv r) (syn_csset) p0011
  have p0036 :=
    @g_opelssetsn (.cv p) (.cv r) p0022 p0001
  have p0037_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r)) :=
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
      p0036
  have p0037 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r) p0034 p0035 p0037_e02_recanon
  have p0038 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem p r) p0032 p0037
  have p0039 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)) p0020 p0038
  have p0040 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)) p p0039
  have p0041 :=
    @g_elima1c p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) dv_cache_0007 dv_cache_0008
  have p0042 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv y))))
  have p0043 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p (syn_cop (.cv x) (.cv y)) (.cv r) dv_cache_0009 dv_cache_0010))
  have p0044_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)))) :=
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
      p0043
  have p0044 :=
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r))) p0042 p0044_e01_recanon
  have p0045 :=
    @g_n_3bitr4i (syn_wex p (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv x) (.cv r) (.cv y)) p0040 p0041 p0044
  have p0046 :=
    @g_elin (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0047 :=
    @g_oqelins4 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (syn_csi3 (syn_cid)) p0001
  have p0048 :=
    @g_otsnelsi3 (.cv p) (.cv y) (.cv x) (syn_cid) p0022 p0014 p0007
  have p0049 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cid) (syn_cop (.cv y) (.cv x)))))
  have p0050 :=
    @g_opex (.cv y) (.cv x) p0014 p0007
  have p0051 :=
    @g_ideq (.cv p) (syn_cop (.cv y) (.cv x)) p0050
  have p0052 :=
    @g_n_3bitr2i (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_csi3 (syn_cid))) (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cid)) (syn_wbr (.cv p) (syn_cid) (syn_cop (.cv y) (.cv x))) (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) p0048 p0049 p0051
  have p0053 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_csi3 (syn_cid))) (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) p0047 p0052
  have p0054 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem p r) p0053 p0037
  have p0055 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)) p0046 p0054
  have p0056 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)) p p0055
  have p0057 :=
    @g_elima1c p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) dv_cache_0007 dv_cache_0011
  have p0058 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv x))))
  have p0059 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p (syn_cop (.cv y) (.cv x)) (.cv r) dv_cache_0012 dv_cache_0010))
  have p0060_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)))) :=
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
      p0059
  have p0060 :=
    @g_bitri (syn_wbr (.cv y) (.cv r) (.cv x)) (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r))) p0058 p0060_e01_recanon
  have p0061 :=
    @g_n_3bitr4i (syn_wex p (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv y) (.cv r) (.cv x)) p0056 p0057 p0060
  have p0062 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv x) (.cv r) (.cv y)) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv y) (.cv r) (.cv x)) p0045 p0061
  have p0063 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) p0019 p0062
  have p0064 :=
    @g_otelins3 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (syn_cid) p0001
  have p0065 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv x)))))
  have p0066 :=
    @g_ideq (syn_csn (.cv y)) (syn_csn (.cv x)) p0011
  have p0067 :=
    @g_eqcom (syn_csn (.cv y)) (syn_csn (.cv x))
  have p0068 :=
    @g_sneqb (.cv x) (.cv y) p0007
  have p0069_e02_recanon : Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv x)) (syn_csn (.cv y))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0068
  have p0069 :=
    @g_n_3bitri (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv x))) (.classEq (syn_csn (.cv y)) (syn_csn (.cv x))) (.classEq (syn_csn (.cv x)) (syn_csn (.cv y))) (.objEq x y) p0066 p0067 p0069_e02_recanon
  have p0070 :=
    @g_n_3bitr2i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cins3 (syn_cid))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_cid)) (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv x))) (.objEq x y) p0064 p0065 p0069
  have p0071 :=
    @g_notbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cins3 (syn_cid))) (.objEq x y) p0070
  have p0072 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cins3 (syn_cid)))) (.neg (.objEq x y)) p0063 p0071
  have p0073 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (.neg (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cins3 (syn_cid))))) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y))) p0017 p0018 p0072
  have p0074 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem y a) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y))) p0016 p0073
  have p0075 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))))) (syn_wa (.objMem y a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y)))) p0010 p0074
  have p0076 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))))) (syn_wa (.objMem y a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y)))) y p0075
  have p0077 :=
    @g_elima1c y (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) dv_cache_0013 dv_cache_0014
  have p0078 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (.cv a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y))))))
  have p0079_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex y (.cv a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y)))) (syn_wex y (syn_wa (.objMem y a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0078
  have p0079 :=
    @g_n_3bitr4i (syn_wex y (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))))) (syn_wex y (syn_wa (.objMem y a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y))))) (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_wrex y (.cv a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y)))) p0076 p0077 p0079_e02_recanon
  have p0080 :=
    @g_rexanali (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y) y (.cv a)
  have p0081 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_wrex y (.cv a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.neg (.objEq x y)))) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y)))) p0079 p0080
  have p0082 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.objMem x a) (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y)))) p0009 p0081
  have p0083 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c)))) (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))) p0005 p0082
  have p0084 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c)))) (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))) x p0083
  have p0085 :=
    @g_elima1c x (syn_cop (.cv r) (.cv a)) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) dv_cache_0015 dv_cache_0016
  have p0086 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y)))))))
  have p0087_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_wral
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0086
  have p0087 :=
    @g_n_3bitr4i (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y)))))) (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))) (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))) p0084 p0085 p0087_e02_recanon
  have p0088 :=
    @g_rexnal (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))) x (.cv a)
  have p0089 :=
    @g_bitri (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))) (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))) (.neg (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))) p0087 p0088
  have p0090 :=
    @g_con2bii (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))) (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y)))) p0089
  have p0091 :=
    @g_bitr4i (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))) (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))) (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y)))) p0004 p0090
  have p0092 :=
    @g_opabbi2i (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y)))) r a (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0091
  have p0093 :=
    @g_eqtr4i (syn_cantisym) (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))) p0000 p0092
  have p0094 :=
    @g_ssetex
  have p0095 :=
    @g_ins2ex (syn_csset) p0094
  have p0096 :=
    @g_ins2ex (syn_cins2 (syn_csset)) p0095
  have p0097 :=
    @g_n_2ndex
  have p0098 :=
    @g_n_1stex
  have p0099 :=
    @g_txpex (syn_c2nd) (syn_c1st) p0097 p0098
  have p0100 :=
    @g_si3ex (syn_ctxp (syn_c2nd) (syn_c1st)) p0099
  have p0101 :=
    @g_ins4ex (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0100
  have p0102 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))) p0101 p0096
  have p0103 :=
    @g_n_1cex
  have p0104 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c) p0102 p0103
  have p0105 :=
    @g_idex
  have p0106 :=
    @g_si3ex (syn_cid) p0105
  have p0107 :=
    @g_ins4ex (syn_csi3 (syn_cid)) p0106
  have p0108 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))) p0107 p0096
  have p0109 :=
    @g_n_1cex
  have p0110 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c) p0108 p0109
  have p0111 :=
    @g_inex (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) p0104 p0110
  have p0112 :=
    @g_idex
  have p0113 :=
    @g_ins3ex (syn_cid) p0112
  have p0114 :=
    @g_difex (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)) p0111 p0113
  have p0115 :=
    @g_ins4ex (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))) p0114
  have p0116 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))) p0096 p0115
  have p0117 :=
    @g_n_1cex
  have p0118 :=
    @g_imaex (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c) p0116 p0117
  have p0119 :=
    @g_inex (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c)) p0095 p0118
  have p0120 :=
    @g_n_1cex
  have p0121 :=
    @g_imaex (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c) p0119 p0120
  have p0122 :=
    @g_complex (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)) p0121
  have p0123 :=
    @g_eqeltri (syn_cantisym) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))) (syn_cvv) p0093 p0122
  exact p0123

#print axioms g_antisymex

end NFChoice.DirectNominalPrf.WPPReplay
