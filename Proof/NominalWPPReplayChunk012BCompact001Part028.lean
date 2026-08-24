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
import NominalWPPReplayChunk012BCompact001Part027

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

noncomputable def g_composeex
     :
    Nominal.NPrf (.classMem (syn_ccompose) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let u : Var := freshVar proofSupport 4
  let t : Var := freshVar proofSupport 5
  let v : Var := freshVar proofSupport 6
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
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_v : v ∉ proofSupport := by
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
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_x_ne_v : x ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
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
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_y_ne_v : y ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_z_ne_v : z ≠ v := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have fresh_w_ne_u : w ≠ u := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_w_ne_v : w ≠ v := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_v_ne_w : v ≠ w :=
    Ne.symm fresh_w_ne_v
  have fresh_u_ne_t : u ≠ t := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_t_ne_u : t ≠ u :=
    Ne.symm fresh_u_ne_t
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_t_ne_v : t ≠ v := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_v_ne_t : v ≠ t :=
    Ne.symm fresh_t_ne_v
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : w ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show w ≠ t from (by exact fresh_w_ne_t))
  have dv_cache_0011 : w ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show w ≠ u from (by exact fresh_w_ne_u))
  have dv_cache_0012 : t ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0013 : w ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_x, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : t ∉ ((syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : u ∉ ((syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_t, fresh_u_ne_w, fresh_u_ne_z, fresh_u_ne_x, fresh_u_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : u ∉ ((syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : t ∉ ((syn_cop (.cv w) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : t ∉ ((syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_u, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : t ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : v ∉ ((syn_cop (.cv u) (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : v ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : v ∉ ((syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_t, fresh_v_ne_w, fresh_v_ne_z, fresh_v_ne_x, fresh_v_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : v ∉ ((syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : x ∉ ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : y ∉ ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : z ∉ ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : z ∉ ((syn_ccom (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0033 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_compose x y dv_cache_0001
  have p0001 :=
    @g_elopab (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))) w t (.cv z) dv_cache_0002 dv_cache_0003
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co w t u (.cv x) (.cv y) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0003 :=
    @g_eleq2i (syn_ccom (.cv x) (.cv y)) (syn_copab w t (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))) (.cv z) p0002
  have p0004 :=
    @g_elima1c w (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) dv_cache_0013 dv_cache_0014
  have p0005 :=
    @g_elima1c t (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) dv_cache_0015 dv_cache_0016
  have p0006 :=
    @g_elin (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_vex y
  have p0009 :=
    @g_opex (.cv x) (.cv y) p0007 p0008
  have p0010 :=
    @g_oqelins4 (syn_csn (.cv t)) (syn_csn (.cv w)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))))) p0009
  have p0011 :=
    @g_vex t
  have p0012 :=
    @g_vex w
  have p0013 :=
    @g_vex z
  have p0014 :=
    @g_otsnelsi3 (.cv t) (.cv w) (.cv z) (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))) p0011 p0012 p0013
  have p0015 :=
    @g_elin (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))
  have p0016 :=
    @g_opelxp (.cv t) (syn_cop (.cv w) (.cv z)) (syn_cvv) (syn_ccnv (syn_c1st))
  have p0017 :=
    @g_mpbiran (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))) (.classMem (.cv t) (syn_cvv)) (.classMem (syn_cop (.cv w) (.cv z)) (syn_ccnv (syn_c1st))) p0011 p0016
  have p0018 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv w) (syn_ccnv (syn_c1st)) (.cv z))))
  have p0019 :=
    @g_brcnv (.cv w) (.cv z) (syn_c1st)
  have p0020 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))) (.classMem (syn_cop (.cv w) (.cv z)) (syn_ccnv (syn_c1st))) (syn_wbr (.cv w) (syn_ccnv (syn_c1st)) (.cv z)) (syn_wbr (.cv z) (syn_c1st) (.cv w)) p0017 p0018 p0019
  have p0021 :=
    @g_otelins2 (.cv t) (.cv w) (.cv z) (syn_ccnv (syn_c2nd)) p0012
  have p0022 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (.cv z))))
  have p0023 :=
    @g_brcnv (.cv t) (.cv z) (syn_c2nd)
  have p0024 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cins2 (syn_ccnv (syn_c2nd)))) (.classMem (syn_cop (.cv t) (.cv z)) (syn_ccnv (syn_c2nd))) (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (.cv z)) (syn_wbr (.cv z) (syn_c2nd) (.cv t)) p0021 p0022 p0023
  have p0025 :=
    @g_anbi12i (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))) (syn_wbr (.cv z) (syn_c1st) (.cv w)) (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cins2 (syn_ccnv (syn_c2nd)))) (syn_wbr (.cv z) (syn_c2nd) (.cv t)) p0020 p0024
  have p0026 :=
    @g_op1st2nd (.cv w) (.cv t) (.cv z) p0012 p0011
  have p0027 :=
    @g_n_3bitri (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))))) (syn_wa (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))) (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cins2 (syn_ccnv (syn_c2nd))))) (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv w)) (syn_wbr (.cv z) (syn_c2nd) (.cv t))) (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) p0015 p0025 p0026
  have p0028 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))))))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_csn (.cv z)))) (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))))) (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) p0010 p0014 p0027
  have p0029 :=
    @g_elima1c u (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) dv_cache_0017 dv_cache_0018
  have p0030 :=
    @g_elin (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))
  have p0031 :=
    @g_snex (.cv t)
  have p0032 :=
    @g_otelins2 (syn_csn (.cv u)) (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)) p0031
  have p0033 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV t (syn_cop (.cv w) (.cv u)) (.cv y) dv_cache_0019 dv_cache_0008))
  have p0034 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv w) (.cv y) (.cv u))))
  have p0035 :=
    @g_elima1c t (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) dv_cache_0020 dv_cache_0021
  have p0036 :=
    @g_elin (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))
  have p0037 :=
    @g_snex (.cv z)
  have p0038 :=
    @g_opex (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) p0037 p0009
  have p0039 :=
    @g_oqelins4 (syn_csn (.cv t)) (syn_csn (.cv u)) (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_csi3 (syn_cswap)) p0038
  have p0040 :=
    @g_vex u
  have p0041 :=
    @g_otsnelsi3 (.cv t) (.cv u) (.cv w) (syn_cswap) p0011 p0040 p0012
  have p0042 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv t) (syn_cswap) (syn_cop (.cv u) (.cv w)))))
  have p0043 :=
    @g_brswap2 (.cv t) (.cv u) (.cv w) p0040 p0012
  have p0044 :=
    @g_n_3bitr2i (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_csn (.cv w)))) (syn_csi3 (syn_cswap))) (.classMem (syn_cop (.cv t) (syn_cop (.cv u) (.cv w))) (syn_cswap)) (syn_wbr (.cv t) (syn_cswap) (syn_cop (.cv u) (.cv w))) (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) p0041 p0042 p0043
  have p0045 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins4 (syn_csi3 (syn_cswap)))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_csn (.cv w)))) (syn_csi3 (syn_cswap))) (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) p0039 p0044
  have p0046 :=
    @g_snex (.cv u)
  have p0047 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) p0046
  have p0048 :=
    @g_snex (.cv w)
  have p0049 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_cins2 (syn_csset))) p0048
  have p0050 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) (syn_cins2 (syn_csset)) p0037
  have p0051 :=
    @g_otelins2 (syn_csn (.cv t)) (.cv x) (.cv y) (syn_csset) p0007
  have p0052 :=
    @g_opelssetsn (.cv t) (.cv y) p0011 p0008
  have p0053_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv t)) (.cv y)) (syn_csset)) (.objMem t y)) :=
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
      p0052
  have p0053 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv t)) (.cv y)) (syn_csset)) (.objMem t y) p0050 p0051 p0053_e02_recanon
  have p0054 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem t y) p0047 p0049 p0053
  have p0055 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins4 (syn_csi3 (syn_cswap)))) (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (.objMem t y) p0045 p0054
  have p0056 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins4 (syn_csi3 (syn_cswap)))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))) (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y)) p0036 p0055
  have p0057 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))) (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y)) t p0056
  have p0058 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_wex t (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))))) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y))) p0035 p0057
  have p0059_e00_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv w) (.cv u)) (.cv y)) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y)))) :=
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
      p0033
  have p0059 :=
    @g_n_3bitr4ri (.classMem (syn_cop (.cv w) (.cv u)) (.cv y)) (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y))) (syn_wbr (.cv w) (.cv y) (.cv u)) (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) p0059_e00_recanon p0034 p0058
  have p0060 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))) (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_wbr (.cv w) (.cv y) (.cv u)) p0032 p0059
  have p0061 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV v (syn_cop (.cv u) (.cv t)) (.cv x) dv_cache_0022 dv_cache_0023))
  have p0062 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv u) (.cv x) (.cv t))))
  have p0063 :=
    @g_elima1c v (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) dv_cache_0024 dv_cache_0025
  have p0064 :=
    @g_elin (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
  have p0065 :=
    @g_opex (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) p0048 p0038
  have p0066 :=
    @g_oqelins4 (syn_csn (.cv v)) (syn_csn (.cv u)) (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_csi3 (syn_cid)) p0065
  have p0067 :=
    @g_vex v
  have p0068 :=
    @g_otsnelsi3 (.cv v) (.cv u) (.cv t) (syn_cid) p0067 p0040 p0011
  have p0069 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv v) (syn_cid) (syn_cop (.cv u) (.cv t)))))
  have p0070 :=
    @g_opex (.cv u) (.cv t) p0040 p0011
  have p0071 :=
    @g_ideq (.cv v) (syn_cop (.cv u) (.cv t)) p0070
  have p0072 :=
    @g_n_3bitr2i (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_csn (.cv t)))) (syn_csi3 (syn_cid))) (.classMem (syn_cop (.cv v) (syn_cop (.cv u) (.cv t))) (syn_cid)) (syn_wbr (.cv v) (syn_cid) (syn_cop (.cv u) (.cv t))) (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) p0068 p0069 p0071
  have p0073 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_csn (.cv t)))) (syn_csi3 (syn_cid))) (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) p0066 p0072
  have p0074 :=
    @g_otelins2 (syn_csn (.cv v)) (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))) p0046
  have p0075 :=
    @g_otelins2 (syn_csn (.cv v)) (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))) p0031
  have p0076 :=
    @g_otelins2 (syn_csn (.cv v)) (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_cins3 (syn_csset))) p0048
  have p0077 :=
    @g_otelins2 (syn_csn (.cv v)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) (syn_cins3 (syn_csset)) p0037
  have p0078 :=
    @g_otelins3 (syn_csn (.cv v)) (.cv x) (.cv y) (syn_csset) p0008
  have p0079 :=
    @g_opelssetsn (.cv v) (.cv x) p0067 p0007
  have p0080_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv v)) (.cv x)) (syn_csset)) (.objMem v x)) :=
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
      p0079
  have p0080 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv v)) (.cv x)) (syn_csset)) (.objMem v x) p0078 p0080_e01_recanon
  have p0081 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))) (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins3 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset))) (.objMem v x) p0076 p0077 p0080
  have p0082 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))) (.objMem v x) p0074 p0075 p0081
  have p0083 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (.objMem v x) p0073 p0082
  have p0084 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))) (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x)) p0064 p0083
  have p0085 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))) (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x)) v p0084
  have p0086 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_wex v (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))))) (syn_wex v (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x))) p0063 p0085
  have p0087_e00_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv u) (.cv t)) (.cv x)) (syn_wex v (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x)))) :=
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
      p0061
  have p0087 :=
    @g_n_3bitr4ri (.classMem (syn_cop (.cv u) (.cv t)) (.cv x)) (syn_wex v (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x))) (syn_wbr (.cv u) (.cv x) (.cv t)) (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) p0087_e00_recanon p0062 p0086
  have p0088 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))) (syn_wbr (.cv w) (.cv y) (.cv u)) (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_wbr (.cv u) (.cv x) (.cv t)) p0060 p0087
  have p0089 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))) (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))) (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))) p0030 p0088
  have p0090 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))) (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))) u p0089
  have p0091 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_wex u (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))))) (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))) p0029 p0090
  have p0092 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))))))) (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))) p0028 p0091
  have p0093 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))))))) (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c)))) (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))) p0006 p0092
  have p0094 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c)))) (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))) t p0093
  have p0095 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c))) (syn_wex t (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))))) (syn_wex t (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))))) p0005 p0094
  have p0096 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c))) (syn_wex t (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))))) w p0095
  have p0097 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c))) (syn_wex w (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)))) (syn_wex w (syn_wex t (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))))) p0004 p0096
  have p0098 :=
    @g_n_3bitr4ri (.classMem (.cv z) (syn_copab w t (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))))) (syn_wex w (syn_wex t (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))))) (.classMem (.cv z) (syn_ccom (.cv x) (.cv y))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c))) p0001 p0003 p0097
  have p0099 :=
    @g_releqmpt2 x y z (syn_cvv) (syn_cvv) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c)) (syn_ccom (.cv x) (.cv y)) dv_cache_0026 dv_cache_0027 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0001 dv_cache_0032 dv_cache_0033 p0098
  have p0100 :=
    @g_eqtr4i (syn_ccompose) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_ccom (.cv x) (.cv y))) (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c)))) (syn_c1c))) p0000 p0099
  have p0101 :=
    @g_vvex
  have p0102 :=
    @g_vvex
  have p0103 :=
    @g_vvex
  have p0104 :=
    @g_n_1stex
  have p0105 :=
    @g_cnvex (syn_c1st) p0104
  have p0106 :=
    @g_xpex (syn_cvv) (syn_ccnv (syn_c1st)) p0103 p0105
  have p0107 :=
    @g_n_2ndex
  have p0108 :=
    @g_cnvex (syn_c2nd) p0107
  have p0109 :=
    @g_ins2ex (syn_ccnv (syn_c2nd)) p0108
  have p0110 :=
    @g_inex (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))) p0106 p0109
  have p0111 :=
    @g_si3ex (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))) p0110
  have p0112 :=
    @g_ins4ex (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))))) p0111
  have p0113 :=
    @g_swapex
  have p0114 :=
    @g_si3ex (syn_cswap) p0113
  have p0115 :=
    @g_ins4ex (syn_csi3 (syn_cswap)) p0114
  have p0116 :=
    @g_ssetex
  have p0117 :=
    @g_ins2ex (syn_csset) p0116
  have p0118 :=
    @g_ins2ex (syn_cins2 (syn_csset)) p0117
  have p0119 :=
    @g_ins2ex (syn_cins2 (syn_cins2 (syn_csset))) p0118
  have p0120 :=
    @g_ins2ex (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) p0119
  have p0121 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) p0115 p0120
  have p0122 :=
    @g_n_1cex
  have p0123 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c) p0121 p0122
  have p0124 :=
    @g_ins2ex (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)) p0123
  have p0125 :=
    @g_idex
  have p0126 :=
    @g_si3ex (syn_cid) p0125
  have p0127 :=
    @g_ins4ex (syn_csi3 (syn_cid)) p0126
  have p0128 :=
    @g_ssetex
  have p0129 :=
    @g_ins3ex (syn_csset) p0128
  have p0130 :=
    @g_ins2ex (syn_cins3 (syn_csset)) p0129
  have p0131 :=
    @g_ins2ex (syn_cins2 (syn_cins3 (syn_csset))) p0130
  have p0132 :=
    @g_ins2ex (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))) p0131
  have p0133 :=
    @g_ins2ex (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))) p0132
  have p0134 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) p0127 p0133
  have p0135 :=
    @g_n_1cex
  have p0136 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c) p0134 p0135
  have p0137 :=
    @g_inex (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)) p0124 p0136
  have p0138 :=
    @g_n_1cex
  have p0139 :=
    @g_imaex (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c) p0137 p0138
  have p0140 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c)) p0112 p0139
  have p0141 :=
    @g_n_1cex
  have p0142 :=
    @g_imaex (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c) p0140 p0141
  have p0143 :=
    @g_n_1cex
  have p0144 :=
    @g_imaex (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c) p0142 p0143
  have p0145 :=
    @g_mpt2exlem (syn_cvv) (syn_cvv) (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c)) p0101 p0102 p0144
  have p0146 :=
    @g_eqeltri (syn_ccompose) (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c)))) (syn_c1c))) (syn_cvv) p0100 p0145
  exact p0146

#print axioms g_composeex

end NFChoice.DirectNominalPrf.WPPReplay
