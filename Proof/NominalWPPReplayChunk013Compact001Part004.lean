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
import NominalWPPReplayChunk013Compact001Part003

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

noncomputable def g_funsex
     :
    Nominal.NPrf (.classMem (syn_cfuns) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let f : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let p : Var := freshVar proofSupport 4
  let q : Var := freshVar proofSupport 5
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_f_ne_x : f ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_f : x ≠ f :=
    Ne.symm fresh_f_ne_x
  have fresh_f_ne_y : f ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_f : y ≠ f :=
    Ne.symm fresh_f_ne_y
  have fresh_f_ne_z : f ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_f : z ≠ f :=
    Ne.symm fresh_f_ne_z
  have fresh_f_ne_p : f ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_p_ne_f : p ≠ f :=
    Ne.symm fresh_f_ne_p
  have fresh_f_ne_q : f ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_q_ne_f : q ≠ f :=
    Ne.symm fresh_f_ne_q
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_p : y ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_y_ne_q : y ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_z_ne_p : z ≠ p := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have fresh_z_ne_q : z ≠ q := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : x ∉ ((Class.cv f)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (syn_csn (.cv x)) (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, fresh_y_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_y, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_x, fresh_q_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, fresh_p_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((syn_csset)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Class.cv f)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Class.cv f)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0018 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0019 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0020 : f ∉ ((syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_funs f
  have p0001 :=
    @g_elima1c x (.cv f) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_snex (.cv x)
  have p0003 :=
    @g_vex f
  have p0004 :=
    @g_opex (syn_csn (.cv x)) (.cv f) p0002 p0003
  have p0005 :=
    @g_elcompl (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c)) p0004
  have p0006 :=
    @g_elima1c z (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) dv_cache_0003 dv_cache_0004
  have p0007 :=
    @g_elima1c y (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) dv_cache_0005 dv_cache_0006
  have p0008 :=
    @g_eldif (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))
  have p0009 :=
    @g_snex (.cv z)
  have p0010 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)) p0009
  have p0011 :=
    @g_vex x
  have p0012 :=
    @g_vex y
  have p0013 :=
    @g_opex (.cv x) (.cv y) p0011 p0012
  have p0014 :=
    @g_opelssetsn (syn_cop (.cv x) (.cv y)) (.cv f) p0013 p0003
  have p0015 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))))
  have p0016 :=
    @g_elin (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))
  have p0017 :=
    @g_oqelins4 (.cv p) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv f) (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)) p0003
  have p0018 :=
    @g_elima1c q (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) dv_cache_0007 dv_cache_0008
  have p0019 :=
    @g_oteltxp (syn_csn (.cv q)) (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))
  have p0020 :=
    @g_opelcnv (syn_csn (.cv q)) (.cv p) (syn_c1st)
  have p0021 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q)))))
  have p0022 :=
    @g_bitr4i (.classMem (syn_cop (syn_csn (.cv q)) (.cv p)) (syn_ccnv (syn_c1st))) (.classMem (syn_cop (.cv p) (syn_csn (.cv q))) (syn_c1st)) (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q))) p0020 p0021
  have p0023 :=
    @g_vex q
  have p0024 :=
    @g_otsnelsi3 (.cv q) (.cv y) (.cv x) (syn_ctxp (syn_c2nd) (syn_c1st)) p0023 p0012 p0011
  have p0025 :=
    @g_oteltxp (.cv q) (.cv y) (.cv x) (syn_c2nd) (syn_c1st)
  have p0026 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv q) (syn_c1st) (.cv x))))
  have p0027 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv q) (syn_c2nd) (.cv y))))
  have p0028 :=
    @g_anbi12i (syn_wbr (.cv q) (syn_c1st) (.cv x)) (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st)) (syn_wbr (.cv q) (syn_c2nd) (.cv y)) (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd)) p0026 p0027
  have p0029 :=
    @g_ancom (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st)) (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd))
  have p0030 :=
    @g_bitr2i (syn_wa (syn_wbr (.cv q) (syn_c1st) (.cv x)) (syn_wbr (.cv q) (syn_c2nd) (.cv y))) (syn_wa (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st)) (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd))) (syn_wa (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd)) (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st))) p0028 p0029
  have p0031 :=
    @g_op1st2nd (.cv x) (.cv y) (.cv q) p0011 p0012
  have p0032 :=
    @g_n_3bitri (.classMem (syn_cop (.cv q) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st))) (syn_wa (.classMem (syn_cop (.cv q) (.cv y)) (syn_c2nd)) (.classMem (syn_cop (.cv q) (.cv x)) (syn_c1st))) (syn_wa (syn_wbr (.cv q) (syn_c1st) (.cv x)) (syn_wbr (.cv q) (syn_c2nd) (.cv y))) (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) p0025 p0030 p0031
  have p0033 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (.classMem (syn_cop (.cv q) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st))) (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) p0024 p0032
  have p0034 :=
    @g_anbi12ci (.classMem (syn_cop (syn_csn (.cv q)) (.cv p)) (syn_ccnv (syn_c1st))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q))) (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) p0022 p0033
  have p0035 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))) (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv q)) (.cv p)) (syn_ccnv (syn_c1st))) (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_wa (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q)))) p0019 p0034
  have p0036 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))) (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (syn_wa (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q)))) q p0035
  have p0037 :=
    @g_sneq (.cv q) (syn_cop (.cv x) (.cv y))
  have p0038 :=
    @g_breq2d (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) (syn_csn (.cv q)) (syn_csn (syn_cop (.cv x) (.cv y))) (.cv p) (syn_c1st) p0037
  have p0039 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y)))) q (syn_cop (.cv x) (.cv y)) dv_cache_0009 dv_cache_0010 p0013 p0038
  have p0040 :=
    @g_n_3bitri (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_wex q (.classMem (syn_cop (syn_csn (.cv q)) (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))) (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))) (syn_wex q (syn_wa (.classEq (.cv q) (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv q))))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y)))) p0018 p0036 p0039
  have p0041 :=
    @g_bitri (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))) (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x)))) (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y)))) p0017 p0040
  have p0042 :=
    @g_otelins2 (.cv p) (syn_csn (.cv x)) (.cv f) (syn_c2nd) p0002
  have p0043 :=
    @g_snex (.cv y)
  have p0044 :=
    @g_otelins2 (.cv p) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cins2 (syn_c2nd)) p0043
  have p0045 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c2nd) (.cv f))))
  have p0046 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cins2 (syn_c2nd))) (.classMem (syn_cop (.cv p) (.cv f)) (syn_c2nd)) (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_wbr (.cv p) (syn_c2nd) (.cv f)) p0042 p0044 p0045
  have p0047 :=
    @g_anbi12i (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y)))) (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_wbr (.cv p) (syn_c2nd) (.cv f)) p0041 p0046
  have p0048 :=
    @g_bitri (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))) (syn_wa (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)))) (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2 (syn_cins2 (syn_c2nd))))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wbr (.cv p) (syn_c2nd) (.cv f))) p0016 p0047
  have p0049 :=
    @g_snex (syn_cop (.cv x) (.cv y))
  have p0050 :=
    @g_op1st2nd (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f) (.cv p) p0049 p0003
  have p0051 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (.classMem (syn_cop (.cv p) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wbr (.cv p) (syn_c2nd) (.cv f))) (.classEq (.cv p) (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f))) p0015 p0048 p0050
  have p0052 :=
    @g_rexbii (syn_wbr (.cv p) (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (.classEq (.cv p) (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f))) p (syn_csset) p0051
  have p0053 :=
    @g_elima p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset) dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0054 :=
    @g_risset p (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f)) (syn_csset) dv_cache_0014 dv_cache_0013
  have p0055 :=
    @g_n_3bitr4i (syn_wrex p (syn_csset) (syn_wbr (.cv p) (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))))) (syn_wrex p (syn_csset) (.classEq (.cv p) (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (.classMem (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f)) (syn_csset)) p0052 p0053 p0054
  have p0056 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (.cv f) (.cv y))))
  have p0057 :=
    @g_n_3bitr4i (.classMem (syn_cop (syn_csn (syn_cop (.cv x) (.cv y))) (.cv f)) (syn_csset)) (.classMem (syn_cop (.cv x) (.cv y)) (.cv f)) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_wbr (.cv x) (.cv f) (.cv y)) p0014 p0055 p0056
  have p0058 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_wbr (.cv x) (.cv f) (.cv y)) p0010 p0057
  have p0059 :=
    @g_otelins3 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cid) p0004
  have p0060 :=
    @g_ideq (syn_csn (.cv y)) (syn_csn (.cv z)) p0009
  have p0061 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z)))))
  have p0062 :=
    @g_sneqb (.cv y) (.cv z) p0012
  have p0063_e02_recanon : Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z)) :=
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
      p0062
  have p0063 :=
    @g_n_3bitr3i (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z))) (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z))) (syn_cid)) (.objEq y z) p0060 p0061 p0063_e02_recanon
  have p0064 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins3 (syn_cid))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z))) (syn_cid)) (.objEq y z) p0059 p0063
  have p0065 :=
    @g_notbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins3 (syn_cid))) (.objEq y z) p0064
  have p0066 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))) (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins3 (syn_cid)))) (.neg (.objEq y z)) p0058 p0065
  have p0067 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)))) (.neg (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cins3 (syn_cid))))) (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z))) p0008 p0066
  have p0068 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)))) (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z))) y p0067
  have p0069 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_wex y (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)))) (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))))) (syn_wex y (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z)))) p0007 p0068
  have p0070 :=
    @g_notbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_wex y (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z)))) p0069
  have p0071 :=
    @g_opex (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f)) p0009 p0004
  have p0072 :=
    @g_elcompl (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c)) p0071
  have p0073 :=
    @g_exanali (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z) y
  have p0074 :=
    @g_con2bii (syn_wex y (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z)))) (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))) p0073
  have p0075 :=
    @g_n_3bitr4i (.neg (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c)))) (.neg (syn_wex y (syn_wa (syn_wbr (.cv x) (.cv f) (.cv y)) (.neg (.objEq y z))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c)))) (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))) p0070 p0072 p0074
  have p0076 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c)))) (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))) z p0075
  have p0077 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv x)) (.cv f))) (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))))) (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))) p0006 p0076
  have p0078 :=
    @g_notbii (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))) p0077
  have p0079 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c)))) (.neg (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c)))) (.neg (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))) p0005 p0078
  have p0080 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c)))) (.neg (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))) x p0079
  have p0081 :=
    @g_bitri (.classMem (.cv f) (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c))) (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (.cv f)) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))))) (syn_wex x (.neg (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))) p0001 p0080
  have p0082 :=
    @g_notbii (.classMem (.cv f) (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c))) (syn_wex x (.neg (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))))) p0081
  have p0083 :=
    @g_elcompl (.cv f) (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)) p0003
  have p0084 :=
    @g_alex (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z)))) x
  have p0085 :=
    @g_n_3bitr4i (.neg (.classMem (.cv f) (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))) (.neg (syn_wex x (.neg (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))))) (.classMem (.cv f) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))) (.all x (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))) p0082 p0083 p0084
  have p0086 :=
    @g_dffun3 x y z (.cv f) dv_cache_0001 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
  have p0087 :=
    @g_bitr4i (.classMem (.cv f) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)))) (.all x (syn_wex z (.all y (.imp (syn_wbr (.cv x) (.cv f) (.cv y)) (.objEq y z))))) (syn_wfun (.cv f)) p0085 p0086
  have p0088 :=
    @g_eqabi (syn_wfun (.cv f)) f (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c))) dv_cache_0020 p0087
  have p0089 :=
    @g_eqtr4i (syn_cfuns) (.cab f (syn_wfun (.cv f))) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c))) p0000 p0088
  have p0090 :=
    @g_n_1stex
  have p0091 :=
    @g_cnvex (syn_c1st) p0090
  have p0092 :=
    @g_n_2ndex
  have p0093 :=
    @g_n_1stex
  have p0094 :=
    @g_txpex (syn_c2nd) (syn_c1st) p0092 p0093
  have p0095 :=
    @g_si3ex (syn_ctxp (syn_c2nd) (syn_c1st)) p0094
  have p0096 :=
    @g_txpex (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0091 p0095
  have p0097 :=
    @g_n_1cex
  have p0098 :=
    @g_imaex (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c) p0096 p0097
  have p0099 :=
    @g_ins4ex (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c)) p0098
  have p0100 :=
    @g_n_2ndex
  have p0101 :=
    @g_ins2ex (syn_c2nd) p0100
  have p0102 :=
    @g_ins2ex (syn_cins2 (syn_c2nd)) p0101
  have p0103 :=
    @g_inex (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd))) p0099 p0102
  have p0104 :=
    @g_ssetex
  have p0105 :=
    @g_imaex (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset) p0103 p0104
  have p0106 :=
    @g_ins2ex (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset)) p0105
  have p0107 :=
    @g_idex
  have p0108 :=
    @g_ins3ex (syn_cid) p0107
  have p0109 :=
    @g_difex (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid)) p0106 p0108
  have p0110 :=
    @g_n_1cex
  have p0111 :=
    @g_imaex (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c) p0109 p0110
  have p0112 :=
    @g_complex (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c)) p0111
  have p0113 :=
    @g_n_1cex
  have p0114 :=
    @g_imaex (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c) p0112 p0113
  have p0115 :=
    @g_complex (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c)) p0114
  have p0116 :=
    @g_n_1cex
  have p0117 :=
    @g_imaex (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c) p0115 p0116
  have p0118 :=
    @g_complex (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c)) p0117
  have p0119 :=
    @g_eqeltri (syn_cfuns) (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_ccompl (syn_cima (syn_cdif (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_cima (syn_ctxp (syn_ccnv (syn_c1st)) (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))) (syn_c1c))) (syn_cins2 (syn_cins2 (syn_c2nd)))) (syn_csset))) (syn_cins3 (syn_cid))) (syn_c1c))) (syn_c1c))) (syn_c1c))) (syn_cvv) p0089 p0118
  exact p0119

noncomputable def g_elfuns
    (F : Class) (hyp_elfuns_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem F (syn_cfuns)) (syn_wfun F)) := by
  let proofSupport : Finset Var := F.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (h)
  have dv_cache_0001 : f ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_funeq (.cv f) F
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_funs f
  have p0002 :=
    @g_elab2 (syn_wfun (.cv f)) (syn_wfun F) f F (syn_cfuns) dv_cache_0001 dv_cache_0002 hyp_elfuns_1 p0000 p0001
  exact p0002

noncomputable def g_elfunsg
    (F : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem F V) (syn_wb (.classMem F (syn_cfuns)) (syn_wfun F))) := by
  let proofSupport : Finset Var := F.fv ∪ V.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_V : f ∉ V.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Wff.classMem F (syn_cfuns))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eleq1 (.cv f) F (syn_cfuns)
  have p0001 :=
    @g_funeq (.cv f) F
  have p0002 :=
    @g_vex f
  have p0003 :=
    @g_elfuns (.cv f) p0002
  have p0004 :=
    @g_vtoclbg (.classMem (.cv f) (syn_cfuns)) (syn_wfun (.cv f)) (.classMem F (syn_cfuns)) (syn_wfun F) f F V dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000 p0001 p0003
  exact p0004

noncomputable def g_elfunsi
    (F : Class) :
    Nominal.NPrf (.imp (.classMem F (syn_cfuns)) (syn_wfun F)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    @g_elfunsg F (syn_cfuns)
  have p0001 :=
    @g_ibi (.classMem F (syn_cfuns)) (syn_wfun F) p0000
  exact p0001

#print axioms g_elfunsi

end NFChoice.DirectNominalPrf.WPPReplay
