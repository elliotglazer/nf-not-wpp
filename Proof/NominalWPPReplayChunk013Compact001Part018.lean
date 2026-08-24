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
import NominalWPPReplayChunk013Compact001Part017

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

noncomputable def g_transex
     :
    Nominal.NPrf (.classMem (syn_ctrans) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let q : Var := freshVar proofSupport 5
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
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
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_y_ne_r : y ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_q : y ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_r_ne_z : r ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_r : z ≠ r :=
    Ne.symm fresh_r_ne_z
  have fresh_r_ne_a : r ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    Ne.symm fresh_r_ne_a
  have fresh_r_ne_q : r ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_q_ne_r : q ≠ r :=
    Ne.symm fresh_r_ne_q
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_q : z ≠ q := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_a_ne_q : a ≠ q := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_q_ne_a : q ≠ a :=
    Ne.symm fresh_a_ne_q
  have dv_cache_0001 : a ≠ r := by
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0004 : a ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0005 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0006 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0007 : r ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0010 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : y ∉ ((syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_r, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, fresh_z_ne_r, fresh_z_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : q ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_z, fresh_q_ne_y, fresh_q_ne_x, fresh_q_ne_r, fresh_q_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, fresh_q_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : q ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : y ∉ ((syn_cop (.cv x) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((syn_cop (.cv r) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : x ∉ ((syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : r ∉ ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : a ∉ ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans x y z r a dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_vex r
  have p0002 :=
    @g_vex a
  have p0003 :=
    @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) p0003
  have p0005 :=
    @g_elin (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))
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
    @g_elima1c y (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) dv_cache_0011 dv_cache_0012
  have p0011 :=
    @g_elin (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))
  have p0012 :=
    @g_snex (.cv x)
  have p0013 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)) (syn_cins2 (syn_csset)) p0012
  have p0014 :=
    @g_otelins2 (syn_csn (.cv y)) (.cv r) (.cv a) (syn_csset) p0001
  have p0015 :=
    @g_vex y
  have p0016 :=
    @g_opelssetsn (.cv y) (.cv a) p0015 p0002
  have p0017_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a)) :=
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
      p0016
  have p0017 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a) p0013 p0014 p0017_e02_recanon
  have p0018 :=
    @g_elima1c z (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) dv_cache_0013 dv_cache_0014
  have p0019 :=
    @g_elin (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
  have p0020 :=
    @g_snex (.cv y)
  have p0021 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_cins2 (syn_csset))) p0020
  have p0022 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)) (syn_cins2 (syn_csset)) p0012
  have p0023 :=
    @g_otelins2 (syn_csn (.cv z)) (.cv r) (.cv a) (syn_csset) p0001
  have p0024 :=
    @g_vex z
  have p0025 :=
    @g_opelssetsn (.cv z) (.cv a) p0024 p0002
  have p0026_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv a)) (syn_csset)) (.objMem z a)) :=
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
      p0025
  have p0026 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (.cv a)) (syn_csset)) (.objMem z a) p0023 p0026_e01_recanon
  have p0027 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.objMem z a) p0021 p0022 p0026
  have p0028 :=
    @g_eldif (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
  have p0029 :=
    @g_elin (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))
  have p0030 :=
    @g_snex (.cv z)
  have p0031 :=
    @g_opelxp (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
  have p0032 :=
    @g_mpbiran (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (.classMem (syn_csn (.cv z)) (syn_cvv)) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) p0030 p0031
  have p0033 :=
    @g_oqelins4 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (.cv a) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) p0002
  have p0034 :=
    @g_elin (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0035 :=
    @g_oqelins4 (syn_csn (.cv z)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0001
  have p0036 :=
    @g_otsnelsi3 (.cv z) (.cv y) (.cv x) (syn_ctxp (syn_c2nd) (syn_c1st)) p0024 p0015 p0007
  have p0037 :=
    @g_oteltxp (.cv z) (.cv y) (.cv x) (syn_c2nd) (syn_c1st)
  have p0038 :=
    @g_ancom (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd)) (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st))
  have p0039 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv z) (syn_c1st) (.cv x))))
  have p0040 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv z) (syn_c2nd) (.cv y))))
  have p0041 :=
    @g_anbi12i (syn_wbr (.cv z) (syn_c1st) (.cv x)) (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st)) (syn_wbr (.cv z) (syn_c2nd) (.cv y)) (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd)) p0039 p0040
  have p0042 :=
    @g_bitr4i (syn_wa (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd)) (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st))) (syn_wa (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st)) (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd))) (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv x)) (syn_wbr (.cv z) (syn_c2nd) (.cv y))) p0038 p0041
  have p0043 :=
    @g_op1st2nd (.cv x) (.cv y) (.cv z) p0007 p0015
  have p0044 :=
    @g_n_3bitri (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st))) (syn_wa (.classMem (syn_cop (.cv z) (.cv y)) (syn_c2nd)) (.classMem (syn_cop (.cv z) (.cv x)) (syn_c1st))) (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv x)) (syn_wbr (.cv z) (syn_c2nd) (.cv y))) (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) p0037 p0042 p0043
  have p0045 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st))) (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) p0035 p0036 p0044
  have p0046 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_cins2 (syn_csset)) p0020
  have p0047 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv r) (syn_csset) p0012
  have p0048 :=
    @g_opelssetsn (.cv z) (.cv r) p0024 p0001
  have p0049_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv r)) (syn_csset)) (.objMem z r)) :=
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
      p0048
  have p0049 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (.cv r)) (syn_csset)) (.objMem z r) p0046 p0047 p0049_e02_recanon
  have p0050 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem z r) p0045 p0049
  have p0051 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r)) p0034 p0050
  have p0052 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r)) z p0051
  have p0053 :=
    @g_elima1c z (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) dv_cache_0015 dv_cache_0016
  have p0054 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv y))))
  have p0055 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV z (syn_cop (.cv x) (.cv y)) (.cv r) dv_cache_0017 dv_cache_0018))
  have p0056_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (.cv r)) (syn_wex z (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r)))) :=
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
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (.cv r)) (syn_wex z (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r))) p0054 p0056_e01_recanon
  have p0057 :=
    @g_n_3bitr4i (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wex z (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.objMem z r))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv x) (.cv r) (.cv y)) p0052 p0053 p0056
  have p0058 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv x) (.cv r) (.cv y)) p0032 p0033 p0057
  have p0059 :=
    @g_elin (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))
  have p0060 :=
    @g_opex (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)) p0012 p0003
  have p0061 :=
    @g_oqelins4 (syn_csn (.cv q)) (syn_csn (.cv z)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0060
  have p0062 :=
    @g_vex q
  have p0063 :=
    @g_otsnelsi3 (.cv q) (.cv z) (.cv y) (syn_ctxp (syn_c2nd) (syn_c1st)) p0062 p0024 p0015
  have p0064 :=
    @g_oteltxp (.cv q) (.cv z) (.cv y) (syn_c2nd) (syn_c1st)
  have p0065 :=
    @g_ancom (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd)) (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st))
  have p0066 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv q) (syn_c1st) (.cv y))))
  have p0067 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv q) (syn_c2nd) (.cv z))))
  have p0068 :=
    @g_anbi12i (syn_wbr (.cv q) (syn_c1st) (.cv y)) (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st)) (syn_wbr (.cv q) (syn_c2nd) (.cv z)) (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd)) p0066 p0067
  have p0069 :=
    @g_bitr4i (syn_wa (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd)) (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st))) (syn_wa (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st)) (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd))) (syn_wa (syn_wbr (.cv q) (syn_c1st) (.cv y)) (syn_wbr (.cv q) (syn_c2nd) (.cv z))) p0065 p0068
  have p0070 :=
    @g_op1st2nd (.cv y) (.cv z) (.cv q) p0015 p0024
  have p0071 :=
    @g_n_3bitri (.classMem (syn_cop (.cv q) (syn_cop (.cv z) (.cv y))) (syn_ctxp (syn_c2nd) (syn_c1st))) (syn_wa (.classMem (syn_cop (.cv q) (.cv z)) (syn_c2nd)) (.classMem (syn_cop (.cv q) (.cv y)) (syn_c1st))) (syn_wa (syn_wbr (.cv q) (syn_c1st) (.cv y)) (syn_wbr (.cv q) (syn_c2nd) (.cv z))) (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) p0064 p0069 p0070
  have p0072 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y)))) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (.classMem (syn_cop (.cv q) (syn_cop (.cv z) (.cv y))) (syn_ctxp (syn_c2nd) (syn_c1st))) (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) p0061 p0063 p0071
  have p0073 :=
    @g_otelins2 (syn_csn (.cv q)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))) p0030
  have p0074 :=
    @g_otelins2 (syn_csn (.cv q)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_cins3 (syn_csset))) p0020
  have p0075 :=
    @g_otelins2 (syn_csn (.cv q)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)) (syn_cins3 (syn_csset)) p0012
  have p0076 :=
    @g_otelins3 (syn_csn (.cv q)) (.cv r) (.cv a) (syn_csset) p0002
  have p0077 :=
    @g_opelssetsn (.cv q) (.cv r) p0062 p0001
  have p0078_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv q)) (.cv r)) (syn_csset)) (.objMem q r)) :=
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
      p0077
  have p0078 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins3 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (.cv r) (.cv a))) (syn_cins3 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv q)) (.cv r)) (syn_csset)) (.objMem q r) p0075 p0076 p0078_e02_recanon
  have p0079 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))) (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins3 (syn_csset)))) (.objMem q r) p0073 p0074 p0078
  have p0080 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (.objMem q r) p0072 p0079
  have p0081 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r)) p0059 p0080
  have p0082 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r)) q p0081
  have p0083 :=
    @g_elima1c q (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) dv_cache_0019 dv_cache_0020
  have p0084 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv z))))
  have p0085 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV q (syn_cop (.cv y) (.cv z)) (.cv r) dv_cache_0021 dv_cache_0022))
  have p0086_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv y) (.cv z)) (.cv r)) (syn_wex q (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r)))) :=
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
      p0085
  have p0086 :=
    @g_bitri (syn_wbr (.cv y) (.cv r) (.cv z)) (.classMem (syn_cop (.cv y) (.cv z)) (.cv r)) (syn_wex q (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r))) p0084 p0086_e01_recanon
  have p0087 :=
    @g_n_3bitr4i (syn_wex q (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))) (syn_wex q (syn_wa (.classEq (.cv q) (syn_cop (.cv y) (.cv z))) (.objMem q r))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_wbr (.cv y) (.cv r) (.cv z)) p0082 p0083 p0086
  have p0088 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_wbr (.cv x) (.cv r) (.cv y)) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_wbr (.cv y) (.cv r) (.cv z)) p0058 p0087
  have p0089 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))) (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) p0029 p0088
  have p0090 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) p0020
  have p0091 :=
    @g_oqelins4 (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv r) (.cv a) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) p0002
  have p0092 :=
    @g_elin (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0093 :=
    @g_oqelins4 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv r) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0001
  have p0094 :=
    @g_otsnelsi3 (.cv y) (.cv z) (.cv x) (syn_ctxp (syn_c2nd) (syn_c1st)) p0015 p0024 p0007
  have p0095 :=
    @g_ancom (.classMem (syn_cop (.cv y) (.cv z)) (syn_c2nd)) (.classMem (syn_cop (.cv y) (.cv x)) (syn_c1st))
  have p0096 :=
    @g_oteltxp (.cv y) (.cv z) (.cv x) (syn_c2nd) (syn_c1st)
  have p0097 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv y) (syn_c1st) (.cv x))))
  have p0098 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv y) (syn_c2nd) (.cv z))))
  have p0099 :=
    @g_anbi12i (syn_wbr (.cv y) (syn_c1st) (.cv x)) (.classMem (syn_cop (.cv y) (.cv x)) (syn_c1st)) (syn_wbr (.cv y) (syn_c2nd) (.cv z)) (.classMem (syn_cop (.cv y) (.cv z)) (syn_c2nd)) p0097 p0098
  have p0100 :=
    @g_n_3bitr4i (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (syn_c2nd)) (.classMem (syn_cop (.cv y) (.cv x)) (syn_c1st))) (syn_wa (.classMem (syn_cop (.cv y) (.cv x)) (syn_c1st)) (.classMem (syn_cop (.cv y) (.cv z)) (syn_c2nd))) (.classMem (syn_cop (.cv y) (syn_cop (.cv z) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st))) (syn_wa (syn_wbr (.cv y) (syn_c1st) (.cv x)) (syn_wbr (.cv y) (syn_c2nd) (.cv z))) p0095 p0096 p0099
  have p0101 :=
    @g_op1st2nd (.cv x) (.cv z) (.cv y) p0007 p0024
  have p0102 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv x)))) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (.classMem (syn_cop (.cv y) (syn_cop (.cv z) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st))) (syn_wa (syn_wbr (.cv y) (syn_c1st) (.cv x)) (syn_wbr (.cv y) (syn_c2nd) (.cv z))) (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) p0094 p0100 p0101
  have p0103 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv x)))) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) p0093 p0102
  have p0104 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_cins2 (syn_csset)) p0030
  have p0105 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (syn_csset) p0012
  have p0106 :=
    @g_opelssetsn (.cv y) (.cv r) p0015 p0001
  have p0107_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_csset)) (.objMem y r)) :=
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
      p0106
  have p0107 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_csset)) (.objMem y r) p0104 p0105 p0107_e02_recanon
  have p0108 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem y r) p0103 p0107
  have p0109 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r)) p0092 p0108
  have p0110 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))))) (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r)) y p0109
  have p0111 :=
    @g_elima1c y (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) dv_cache_0023 dv_cache_0024
  have p0112 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv z))))
  have p0113 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y (syn_cop (.cv x) (.cv z)) (.cv r) dv_cache_0025 dv_cache_0026))
  have p0114_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) (.cv z)) (.cv r)) (syn_wex y (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r)))) :=
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
      p0113
  have p0114 :=
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv z)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv r)) (syn_wex y (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r))) p0112 p0114_e01_recanon
  have p0115 :=
    @g_n_3bitr4i (syn_wex y (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r)))) (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_wex y (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv z))) (.objMem y r))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv x) (.cv r) (.cv z)) p0110 p0111 p0114
  have p0116 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_wbr (.cv x) (.cv r) (.cv z)) p0090 p0091 p0115
  have p0117 :=
    @g_notbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_wbr (.cv x) (.cv r) (.cv z)) p0116
  have p0118 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))) (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z))) p0089 p0117
  have p0119 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)))) (.neg (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z)))) p0028 p0118
  have p0120 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (.objMem z a) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z)))) p0027 p0119
  have p0121 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))) (syn_wa (.objMem z a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))) p0019 p0120
  have p0122 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))) (syn_wa (.objMem z a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))) z p0121
  have p0123 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex z (.cv a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z)))))))
  have p0124 :=
    @g_rexanali (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)) z (.cv a)
  have p0125_e00_recanon : Nominal.NPrf (syn_wb (syn_wrex z (.cv a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))) (syn_wex z (syn_wa (.objMem z a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0123
  have p0125 :=
    @g_bitr3i (syn_wex z (syn_wa (.objMem z a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z)))))) (syn_wrex z (.cv a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z))))) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))) p0125_e00_recanon p0124
  have p0126 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))) (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))))) (syn_wex z (syn_wa (.objMem z a) (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (.neg (syn_wbr (.cv x) (.cv r) (.cv z)))))) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))) p0018 p0122 p0125
  have p0127 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem y a) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))) p0017 p0126
  have p0128 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))) (syn_wa (.objMem y a) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) p0011 p0127
  have p0129 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)))) (syn_wa (.objMem y a) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) y p0128
  have p0130 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (.cv a) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))))
  have p0131 :=
    @g_rexnal (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))) y (.cv a)
  have p0132_e00_recanon : Nominal.NPrf (syn_wb (syn_wrex y (.cv a) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0130
  have p0132 :=
    @g_bitr3i (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))) (syn_wrex y (.cv a) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) p0132_e00_recanon p0131
  have p0133 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_wex y (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))))) (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) p0010 p0129 p0132
  have p0134 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.objMem x a) (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) p0009 p0133
  have p0135 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c)))) (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))) p0005 p0134
  have p0136 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c)))) (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))) x p0135
  have p0137 :=
    @g_elima1c x (syn_cop (.cv r) (.cv a)) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) dv_cache_0027 dv_cache_0028
  have p0138 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))))))
  have p0139_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_wral
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0138
  have p0139 :=
    @g_n_3bitr4i (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))))) (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c))) (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))) p0136 p0137 p0139_e02_recanon
  have p0140 :=
    @g_rexnal (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))) x (.cv a)
  have p0141 :=
    @g_bitri (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c))) (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))) (.neg (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))) p0139 p0140
  have p0142 :=
    @g_con2bii (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c))) (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) p0141
  have p0143 :=
    @g_bitr4i (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c)))) (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c)))) (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) p0004 p0142
  have p0144 :=
    @g_opabbi2i (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) r a (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c))) dv_cache_0029 dv_cache_0030 dv_cache_0031 p0143
  have p0145 :=
    @g_eqtr4i (syn_ctrans) (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))))))) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c))) p0000 p0144
  have p0146 :=
    @g_ssetex
  have p0147 :=
    @g_ins2ex (syn_csset) p0146
  have p0148 :=
    @g_ins2ex (syn_cins2 (syn_csset)) p0147
  have p0149 :=
    @g_ins2ex (syn_cins2 (syn_cins2 (syn_csset))) p0148
  have p0150 :=
    @g_vvex
  have p0151 :=
    @g_n_2ndex
  have p0152 :=
    @g_n_1stex
  have p0153 :=
    @g_txpex (syn_c2nd) (syn_c1st) p0151 p0152
  have p0154 :=
    @g_si3ex (syn_ctxp (syn_c2nd) (syn_c1st)) p0153
  have p0155 :=
    @g_ins4ex (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0154
  have p0156 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset))) p0155 p0148
  have p0157 :=
    @g_n_1cex
  have p0158 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c) p0156 p0157
  have p0159 :=
    @g_ins4ex (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) p0158
  have p0160 :=
    @g_xpex (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) p0150 p0159
  have p0161 :=
    @g_ssetex
  have p0162 :=
    @g_ins3ex (syn_csset) p0161
  have p0163 :=
    @g_ins2ex (syn_cins3 (syn_csset)) p0162
  have p0164 :=
    @g_ins2ex (syn_cins2 (syn_cins3 (syn_csset))) p0163
  have p0165 :=
    @g_ins2ex (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))) p0164
  have p0166 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))) p0155 p0165
  have p0167 :=
    @g_n_1cex
  have p0168 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c) p0166 p0167
  have p0169 :=
    @g_inex (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c)) p0160 p0168
  have p0170 :=
    @g_ins2ex (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) p0159
  have p0171 :=
    @g_difex (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) p0169 p0170
  have p0172 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) p0149 p0171
  have p0173 :=
    @g_n_1cex
  have p0174 :=
    @g_imaex (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c) p0172 p0173
  have p0175 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c)) p0148 p0174
  have p0176 :=
    @g_n_1cex
  have p0177 :=
    @g_imaex (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c) p0175 p0176
  have p0178 :=
    @g_inex (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c)) p0147 p0177
  have p0179 :=
    @g_n_1cex
  have p0180 :=
    @g_imaex (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c) p0178 p0179
  have p0181 :=
    @g_complex (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) p0180
  have p0182 :=
    @g_eqeltri (syn_ctrans) (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (syn_c1c))) (syn_cins2 (syn_cins4 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))) (syn_c1c))) (syn_c1c))) (syn_c1c))) (syn_cvv) p0145 p0181
  exact p0182

#print axioms g_transex

end NFChoice.DirectNominalPrf.WPPReplay
