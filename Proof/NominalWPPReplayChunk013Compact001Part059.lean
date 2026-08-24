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
import NominalWPPReplayChunk013Compact001Part058

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

noncomputable def g_tcfnex
     :
    Nominal.NPrf (.classMem (syn_ctcfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  let u : Var := freshVar proofSupport 5
  let t : Var := freshVar proofSupport 6
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
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
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_p : y ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_y_ne_q : y ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_z_ne_p : z ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have fresh_z_ne_q : z ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have fresh_p_ne_u : p ≠ u := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_u_ne_p : u ≠ p :=
    Ne.symm fresh_p_ne_u
  have fresh_p_ne_t : p ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_t_ne_p : t ≠ p :=
    Ne.symm fresh_p_ne_t
  have fresh_q_ne_u : q ≠ u := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have fresh_q_ne_t : q ≠ t := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_t_ne_q : t ≠ q :=
    Ne.symm fresh_q_ne_t
  have fresh_u_ne_t : u ≠ t := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_t_ne_u : t ≠ u :=
    Ne.symm fresh_u_ne_t
  have dv_cache_0001 : p ∉ ((syn_cop (.cv z) (.cv x))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_z, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.classMem (.cv p) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ ((syn_csn (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_cpw1fn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_wbr (.cv u) (syn_csset) (.cv p))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_u, fresh_t_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((syn_csn (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_ne_t, fresh_u_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((syn_csn (syn_csn (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((syn_csset)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : u ∉ ((syn_csi (syn_cpw1fn))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((syn_cpw1 (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : t ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((syn_cop (syn_csn (syn_csn (.cv q))) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_q, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : t ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((syn_cop (.cv p) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : z ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : z ∉ ((syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : p ∉ ((syn_cuni (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : q ∉ ((syn_cuni (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0027 : z ∉ ((syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_x, fresh_z_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : p ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show p ≠ z from (by exact fresh_p_ne_z))
  have dv_cache_0029 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : x ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : x ∉ ((syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : y ∉ ((syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : y ∉ ((syn_ctc (syn_cuni (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tcfn x
  have p0001 :=
    @g_oteltxp (.cv z) (syn_csn (.cv y)) (.cv x) (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))
  have p0002 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv z) (syn_ccnv (syn_csset)) (syn_csn (.cv y)))))
  have p0003 :=
    @g_brcnv (.cv z) (syn_csn (.cv y)) (syn_csset)
  have p0004 :=
    @g_vex y
  have p0005 :=
    @g_vex z
  have p0006 :=
    @g_brssetsn (.cv y) (.cv z) p0004 p0005
  have p0007_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv z)) (.objMem y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0006
  have p0007 :=
    @g_bitri (syn_wbr (.cv z) (syn_ccnv (syn_csset)) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv y)) (syn_csset) (.cv z)) (.objMem y z) p0003 p0007_e01_recanon
  have p0008 :=
    @g_bitr3i (.classMem (syn_cop (.cv z) (syn_csn (.cv y))) (syn_ccnv (syn_csset))) (syn_wbr (.cv z) (syn_ccnv (syn_csset)) (syn_csn (.cv y))) (.objMem y z) p0002 p0007
  have p0009 :=
    @g_vex x
  have p0010 :=
    @g_opex (.cv z) (.cv x) p0005 p0009
  have p0011 :=
    @g_elcompl (syn_cop (.cv z) (.cv x)) (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))) p0010
  have p0012 :=
    @g_elrn2 p (syn_cop (.cv z) (.cv x)) (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))) dv_cache_0001 dv_cache_0002
  have p0013 :=
    @g_elsymdif (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))
  have p0014 :=
    @g_otelins2 (.cv p) (.cv z) (.cv x) (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))) p0005
  have p0015 :=
    @g_elin (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))
  have p0016 :=
    @g_opelxp (.cv p) (.cv x) (syn_cncs) (syn_cvv)
  have p0017 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv))) (.classMem (.cv p) (syn_cncs)) (.classMem (.cv x) (syn_cvv)) p0009 p0016
  have p0018 :=
    @g_anbi1i (.classMem (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv))) (.classMem (.cv p) (syn_cncs)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))) p0017
  have p0019 :=
    @g_ncseqnc (.cv p) (syn_cpw1 (.cv q))
  have p0020 :=
    @g_rexbidv (.classMem (.cv p) (syn_cncs)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))) (.classMem (syn_cpw1 (.cv q)) (.cv p)) q (syn_cuni (.cv x)) dv_cache_0003 p0019
  have p0021 :=
    @g_oteltxp (syn_csn (syn_csn (.cv q))) (.cv p) (.cv x) (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))
  have p0022 :=
    @g_snex (.cv q)
  have p0023 :=
    @g_brsnsi1 t (syn_csn (.cv q)) (.cv u) (syn_cpw1fn) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0022
  have p0024 :=
    @g_anbi1i (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u)) (syn_wex t (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))) (syn_wbr (.cv u) (syn_csset) (.cv p)) p0023
  have p0025 :=
    @g_n_19_41v (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p)) t dv_cache_0007
  have p0026 :=
    @g_bitr4i (syn_wa (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u)) (syn_wbr (.cv u) (syn_csset) (.cv p))) (syn_wa (syn_wex t (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)))) (syn_wbr (.cv u) (syn_csset) (.cv p))) (syn_wex t (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p)))) p0024 p0025
  have p0027 :=
    @g_exbii (syn_wa (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u)) (syn_wbr (.cv u) (syn_csset) (.cv p))) (syn_wex t (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p)))) u p0026
  have p0028 :=
    @g_excom (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p))) u t
  have p0029 :=
    @g_anass (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) (syn_wbr (.cv u) (syn_csset) (.cv p))
  have p0030 :=
    @g_exbii (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p))) (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) (syn_wbr (.cv u) (syn_csset) (.cv p)))) u p0029
  have p0031 :=
    @g_snex (.cv t)
  have p0032 :=
    @g_breq1 (.cv u) (syn_csn (.cv t)) (.cv p) (syn_csset)
  have p0033 :=
    @g_anbi2d (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p)) (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p)) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) p0032
  have p0034 :=
    @g_ceqsexv (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) (syn_wbr (.cv u) (syn_csset) (.cv p))) (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p))) u (syn_csn (.cv t)) dv_cache_0008 dv_cache_0009 p0031 p0033
  have p0035 :=
    @g_vex q
  have p0036 :=
    @g_brpw1fn (.cv q) (.cv t) p0035
  have p0037 :=
    @g_vex t
  have p0038 :=
    @g_vex p
  have p0039 :=
    @g_brssetsn (.cv t) (.cv p) p0037 p0038
  have p0040_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p)) (.objMem t p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0039
  have p0040 :=
    @g_anbi12i (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) (.classEq (.cv t) (syn_cpw1 (.cv q))) (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p)) (.objMem t p) p0036 p0040_e01_recanon
  have p0041 :=
    @g_n_3bitri (syn_wex u (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p)))) (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) (syn_wbr (.cv u) (syn_csset) (.cv p))))) (syn_wa (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t)) (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv p))) (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p)) p0030 p0034 p0040
  have p0042 :=
    @g_exbii (syn_wex u (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p)))) (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p)) t p0041
  have p0043 :=
    @g_n_3bitri (syn_wex u (syn_wa (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u)) (syn_wbr (.cv u) (syn_csset) (.cv p)))) (syn_wex u (syn_wex t (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p))))) (syn_wex t (syn_wex u (syn_wa (syn_wa (.classEq (.cv u) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv q)) (syn_cpw1fn) (.cv t))) (syn_wbr (.cv u) (syn_csset) (.cv p))))) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p))) p0027 p0028 p0042
  have p0044 :=
    @g_opelco u (syn_csn (syn_csn (.cv q))) (.cv p) (syn_csset) (syn_csi (syn_cpw1fn)) dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0045 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV t (syn_cpw1 (.cv q)) (.cv p) dv_cache_0014 dv_cache_0015))
  have p0046_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cpw1 (.cv q)) (.cv p)) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0045
  have p0046 :=
    @g_n_3bitr4i (syn_wex u (syn_wa (syn_wbr (syn_csn (syn_csn (.cv q))) (syn_csi (syn_cpw1fn)) (.cv u)) (syn_wbr (.cv u) (syn_csset) (.cv p)))) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cpw1 (.cv q))) (.objMem t p))) (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv p)) (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))) (.classMem (syn_cpw1 (.cv q)) (.cv p)) p0043 p0044 p0046_e02_recanon
  have p0047 :=
    @g_oteltxp (syn_csn (.cv t)) (syn_csn (syn_csn (.cv q))) (.cv x) (syn_csi (syn_ccnv (syn_csset))) (syn_csset)
  have p0048 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (.cv t)) (syn_csi (syn_ccnv (syn_csset))) (syn_csn (syn_csn (.cv q))))))
  have p0049 :=
    @g_brsnsi (.cv t) (syn_csn (.cv q)) (syn_ccnv (syn_csset)) p0037 p0022
  have p0050 :=
    @g_brcnv (.cv t) (syn_csn (.cv q)) (syn_csset)
  have p0051 :=
    @g_brssetsn (.cv q) (.cv t) p0035 p0037
  have p0052_e02_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv q)) (syn_csset) (.cv t)) (.objMem q t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0051
  have p0052 :=
    @g_n_3bitri (syn_wbr (syn_csn (.cv t)) (syn_csi (syn_ccnv (syn_csset))) (syn_csn (syn_csn (.cv q)))) (syn_wbr (.cv t) (syn_ccnv (syn_csset)) (syn_csn (.cv q))) (syn_wbr (syn_csn (.cv q)) (syn_csset) (.cv t)) (.objMem q t) p0049 p0050 p0052_e02_recanon
  have p0053 :=
    @g_bitr3i (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (syn_csn (.cv q)))) (syn_csi (syn_ccnv (syn_csset)))) (syn_wbr (syn_csn (.cv t)) (syn_csi (syn_ccnv (syn_csset))) (syn_csn (syn_csn (.cv q)))) (.objMem q t) p0048 p0052
  have p0054 :=
    @g_opelssetsn (.cv t) (.cv x) p0037 p0009
  have p0055_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv t)) (.cv x)) (syn_csset)) (.objMem t x)) :=
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
      p0054
  have p0055 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (syn_csn (.cv q)))) (syn_csi (syn_ccnv (syn_csset)))) (.objMem q t) (.classMem (syn_cop (syn_csn (.cv t)) (.cv x)) (syn_csset)) (.objMem t x) p0053 p0055_e01_recanon
  have p0056 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x))) (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))) (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (syn_csn (.cv q)))) (syn_csi (syn_ccnv (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv t)) (.cv x)) (syn_csset))) (syn_wa (.objMem q t) (.objMem t x)) p0047 p0055
  have p0057 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x))) (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))) (syn_wa (.objMem q t) (.objMem t x)) t p0056
  have p0058 :=
    @g_elima1c t (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x)) (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) dv_cache_0016 dv_cache_0017
  have p0059 :=
    @g_eluni t (.cv q) (.cv x) dv_cache_0018 dv_cache_0019
  have p0060_e02_recanon : Nominal.NPrf (syn_wb (.classMem (.cv q) (syn_cuni (.cv x))) (syn_wex t (syn_wa (.objMem q t) (.objMem t x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0059
  have p0060 :=
    @g_n_3bitr4i (syn_wex t (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x))) (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)))) (syn_wex t (syn_wa (.objMem q t) (.objMem t x))) (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x)) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (.classMem (.cv q) (syn_cuni (.cv x))) p0057 p0058 p0060_e02_recanon
  have p0061 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv p)) (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))) (.classMem (syn_cpw1 (.cv q)) (.cv p)) (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x)) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (.classMem (.cv q) (syn_cuni (.cv x))) p0046 p0060
  have p0062 :=
    @g_ancom (.classMem (syn_cpw1 (.cv q)) (.cv p)) (.classMem (.cv q) (syn_cuni (.cv x)))
  have p0063 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (syn_cop (.cv p) (.cv x))) (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv p)) (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn)))) (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (.cv x)) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))) (syn_wa (.classMem (syn_cpw1 (.cv q)) (.cv p)) (.classMem (.cv q) (syn_cuni (.cv x)))) (syn_wa (.classMem (.cv q) (syn_cuni (.cv x))) (.classMem (syn_cpw1 (.cv q)) (.cv p))) p0021 p0061 p0062
  have p0064 :=
    @g_exbii (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (syn_cop (.cv p) (.cv x))) (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))) (syn_wa (.classMem (.cv q) (syn_cuni (.cv x))) (.classMem (syn_cpw1 (.cv q)) (.cv p))) q p0063
  have p0065 :=
    @g_elimapw11c q (syn_cop (.cv p) (.cv x)) (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) dv_cache_0020 dv_cache_0021
  have p0066 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex q (syn_cuni (.cv x)) (.classMem (syn_cpw1 (.cv q)) (.cv p)))))
  have p0067 :=
    @g_n_3bitr4i (syn_wex q (.classMem (syn_cop (syn_csn (syn_csn (.cv q))) (syn_cop (.cv p) (.cv x))) (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))))) (syn_wex q (syn_wa (.classMem (.cv q) (syn_cuni (.cv x))) (.classMem (syn_cpw1 (.cv q)) (.cv p)))) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))) (syn_wrex q (syn_cuni (.cv x)) (.classMem (syn_cpw1 (.cv q)) (.cv p))) p0064 p0065 p0066
  have p0068 :=
    @g_syl6rbbr (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))) (syn_wrex q (syn_cuni (.cv x)) (.classMem (syn_cpw1 (.cv q)) (.cv p))) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))) p0020 p0067
  have p0069 :=
    @g_pm5_32i (.classMem (.cv p) (syn_cncs)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))) p0068
  have p0070 :=
    @g_bitri (syn_wa (.classMem (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv))) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_wa (.classMem (.cv p) (syn_cncs)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) p0018 p0069
  have p0071 :=
    @g_n_3bitri (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))))) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_wa (.classMem (syn_cop (.cv p) (.cv x)) (syn_cxp (syn_cncs) (syn_cvv))) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) p0014 p0015 p0070
  have p0072 :=
    @g_otelins3 (.cv p) (.cv z) (.cv x) (syn_cid) p0009
  have p0073 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cid) (.cv z))))
  have p0074 :=
    @g_ideq (.cv p) (.cv z) p0005
  have p0075_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv p) (syn_cid) (.cv z)) (.objEq p z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cid syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0074
  have p0075 :=
    @g_bitr3i (.classMem (syn_cop (.cv p) (.cv z)) (syn_cid)) (syn_wbr (.cv p) (syn_cid) (.cv z)) (.objEq p z) p0073 p0075_e01_recanon
  have p0076 :=
    @g_bitri (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins3 (syn_cid))) (.classMem (syn_cop (.cv p) (.cv z)) (syn_cid)) (.objEq p z) p0072 p0075
  have p0077 :=
    @g_bibi12i (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))))) (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins3 (syn_cid))) (.objEq p z) p0071 p0076
  have p0078 :=
    @g_xchbinx (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))) (syn_wb (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))))) (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_cins3 (syn_cid)))) (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)) p0013 p0077
  have p0079 :=
    @g_exbii (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))) (.neg (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))) p p0078
  have p0080 :=
    @g_exnal (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)) p
  have p0081 :=
    @g_n_3bitrri (.classMem (syn_cop (.cv z) (.cv x)) (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))) (syn_wex p (.classMem (syn_cop (.cv p) (syn_cop (.cv z) (.cv x))) (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))) (syn_wex p (.neg (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))) (.neg (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))) p0012 p0079 p0080
  have p0082 :=
    @g_con1bii (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))) (.classMem (syn_cop (.cv z) (.cv x)) (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))) p0081
  have p0083 :=
    @g_bitri (.classMem (syn_cop (.cv z) (.cv x)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))) (.neg (.classMem (syn_cop (.cv z) (.cv x)) (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))) p0011 p0082
  have p0084 :=
    @g_anbi12i (.classMem (syn_cop (.cv z) (syn_csn (.cv y))) (syn_ccnv (syn_csset))) (.objMem y z) (.classMem (syn_cop (.cv z) (.cv x)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))) p0008 p0083
  have p0085 :=
    @g_bitri (.classMem (syn_cop (.cv z) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))) (syn_wa (.classMem (syn_cop (.cv z) (syn_csn (.cv y))) (syn_ccnv (syn_csset))) (.classMem (syn_cop (.cv z) (.cv x)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))) (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))) p0001 p0084
  have p0086 :=
    @g_exbii (.classMem (syn_cop (.cv z) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))) (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))) z p0085
  have p0087 :=
    @g_elrn2 z (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))) dv_cache_0022 dv_cache_0023
  have p0088 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc q (syn_cuni (.cv x)) p dv_cache_0024 dv_cache_0025 dv_cache_0026
  have p0089 :=
    @g_dfiota2 (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) p z dv_cache_0027 dv_cache_0028
  have p0090 :=
    @g_eqtri (syn_ctc (syn_cuni (.cv x))) (syn_cio p (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q))))))) (syn_cuni (.cab z (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))))) p0088 p0089
  have p0091 :=
    @g_eleq2i (syn_ctc (syn_cuni (.cv x))) (syn_cuni (.cab z (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))))) (.cv y) p0090
  have p0092 :=
    @g_eluniab (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))) z (.cv y) dv_cache_0029
  have p0093_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_cuni (.cab z (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))))) (syn_wex z (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0092
  have p0093 :=
    @g_bitri (.classMem (.cv y) (syn_ctc (syn_cuni (.cv x)))) (.classMem (.cv y) (syn_cuni (.cab z (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z)))))) (syn_wex z (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))))) p0091 p0093_e01_recanon
  have p0094 :=
    @g_n_3bitr4i (syn_wex z (.classMem (syn_cop (.cv z) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))) (syn_wex z (syn_wa (.objMem y z) (.all p (syn_wb (syn_wa (.classMem (.cv p) (syn_cncs)) (syn_wrex q (syn_cuni (.cv x)) (.classEq (.cv p) (syn_cnc (syn_cpw1 (.cv q)))))) (.objEq p z))))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))))) (.classMem (.cv y) (syn_ctc (syn_cuni (.cv x)))) p0086 p0087 p0093
  have p0095 :=
    @g_releqmpt x y (syn_c1c) (syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))) (syn_ctc (syn_cuni (.cv x))) dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 p0094
  have p0096 :=
    @g_eqtr4i (syn_ctcfn) (syn_cmpt x (syn_c1c) (syn_ctc (syn_cuni (.cv x)))) (syn_cin (syn_cxp (syn_c1c) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))))) (syn_c1c))))) p0000 p0095
  have p0097 :=
    @g_n_1cex
  have p0098 :=
    @g_ssetex
  have p0099 :=
    @g_cnvex (syn_csset) p0098
  have p0100 :=
    @g_ncsex
  have p0101 :=
    @g_vvex
  have p0102 :=
    @g_xpex (syn_cncs) (syn_cvv) p0100 p0101
  have p0103 :=
    @g_ssetex
  have p0104 :=
    @g_pw1fnex
  have p0105 :=
    @g_siex (syn_cpw1fn) p0104
  have p0106 :=
    @g_coex (syn_csset) (syn_csi (syn_cpw1fn)) p0103 p0105
  have p0107 :=
    @g_siex (syn_ccnv (syn_csset)) p0099
  have p0108 :=
    @g_ssetex
  have p0109 :=
    @g_txpex (syn_csi (syn_ccnv (syn_csset))) (syn_csset) p0107 p0108
  have p0110 :=
    @g_n_1cex
  have p0111 :=
    @g_imaex (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c) p0109 p0110
  have p0112 :=
    @g_txpex (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)) p0106 p0111
  have p0113 :=
    @g_n_1cex
  have p0114 :=
    @g_pw1ex (syn_c1c) p0113
  have p0115 :=
    @g_imaex (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)) p0112 p0114
  have p0116 :=
    @g_inex (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))) p0102 p0115
  have p0117 :=
    @g_ins2ex (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))) p0116
  have p0118 :=
    @g_idex
  have p0119 :=
    @g_ins3ex (syn_cid) p0118
  have p0120 :=
    @g_symdifex (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)) p0117 p0119
  have p0121 :=
    @g_rnex (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))) p0120
  have p0122 :=
    @g_complex (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))) p0121
  have p0123 :=
    @g_txpex (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))) p0099 p0122
  have p0124 :=
    @g_rnex (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid)))))) p0123
  have p0125 :=
    @g_mptexlem (syn_c1c) (syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))) p0097 p0124
  have p0126 :=
    @g_eqeltri (syn_ctcfn) (syn_cin (syn_cxp (syn_c1c) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_crn (syn_ctxp (syn_ccnv (syn_csset)) (syn_ccompl (syn_crn (syn_csymdif (syn_cins2 (syn_cin (syn_cxp (syn_cncs) (syn_cvv)) (syn_cima (syn_ctxp (syn_ccom (syn_csset) (syn_csi (syn_cpw1fn))) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_cins3 (syn_cid))))))))) (syn_c1c))))) (syn_cvv) p0096 p0125
  exact p0126

#print axioms g_tcfnex

end NFChoice.DirectNominalPrf.WPPReplay
