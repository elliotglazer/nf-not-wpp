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
import NominalWPPReplayChunk017Compact001Part080

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

noncomputable def g_hnwcutambstrictsegranimpndv
    (u : Var) (A : Class) (r : Var) (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_r_u : r ≠ u) (hyp_hnwcutstrictsegimp_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classEq (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ ({r} : Finset Var)
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let v : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_z : r ≠ z :=
    Ne.symm fresh_z_ne_r
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_r : v ≠ r := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_v : r ≠ v :=
    Ne.symm fresh_v_ne_r
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_ne_r : w ≠ r := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_w : r ≠ w :=
    Ne.symm fresh_w_ne_r
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_v : z ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_x_ne_v : x ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_v_ne_w : v ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_v : w ≠ v :=
    Ne.symm fresh_v_ne_w
  have fresh_v_ne_y : v ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_w_ne_y : w ≠ y := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0004 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0005 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : v ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0009 : v ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0010 : x ∉ ((syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_A, fresh_x_ne_u, fresh_x_ne_z, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_x, fresh_v_not_A, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : v ∉ ((syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_r, fresh_v_not_A, fresh_v_ne_u, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint (({y} : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (({y} : Finset Var)) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) (({u} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show y ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ u from (by exact fresh_y_ne_u)))))))), (show Disjoint (({y} : Finset Var)) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint (({y} : Finset Var)) ((∅ : Finset Var)) from (by simp))))⟩))))
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_wbr (.cv w) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_x, fresh_y_ne_u, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, fresh_y_not_A, fresh_y_ne_u, fresh_y_ne_x, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : w ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show w ≠ u from (by exact fresh_w_ne_u))
  have dv_cache_0022 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0023 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0024 : w ∉ ((syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_u, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : w ∉ ((syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_r, fresh_w_not_A, fresh_w_ne_u, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((Wff.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, fresh_x_ne_r, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_A, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : z ∉ ((syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : z ∉ ((syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_r, fresh_z_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : z ∉ ((syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_r, fresh_z_not_A, fresh_z_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0001 :=
    @g_hnwcutambfactorranbrimpndv x z u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_hnwcutstrictsegimp_1
  have p0002 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) (syn_wb (.classMem (.cv z) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)))) p0000 p0001
  have p0003 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
  have p0004 :=
    @g_elin (.cv z) (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))
  have p0005 :=
    @g_biimpi (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wa (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0004
  have p0006 :=
    @g_simpl (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
  have p0007 :=
    @g_syl (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wa (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (.classMem (.cv z) (syn_chnord A)) p0005 p0006
  have p0008 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (.classMem (.cv z) (syn_chnord A)) p0003 p0007
  have p0009 :=
    @g_vex z
  have p0010 :=
    @g_elhnordclndv v A (.cv z) dv_cache_0005 dv_cache_0006
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_a1i (syn_wb (.classMem (.cv z) (syn_chnord A)) (syn_wrex v (syn_chwcn A) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) p0011
  have p0013 :=
    @g_mpbid (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (.classMem (.cv z) (syn_chnord A)) (syn_wrex v (syn_chwcn A) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))) p0008 p0012
  have p0014 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0015 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
  have p0016 :=
    @g_elin (.cv z) (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))
  have p0017 :=
    @g_biimpi (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wa (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0016
  have p0018 :=
    @g_simpr (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
  have p0019 :=
    @g_syl (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wa (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) p0017 p0018
  have p0020 :=
    @g_eliniseg (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A)) (.cv z)
  have p0021 :=
    @g_biimpi (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) p0020
  have p0022 :=
    @g_syl (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) p0019 p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) p0015 p0022
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) p0014 p0023
  have p0025 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0026 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) p0025
  have p0027 :=
    @g_breq1d (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.cv z) (syn_cec (.cv v) (syn_chwniso A)) (syn_cec (.cv u) (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) p0026
  have p0028 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (syn_cec (.cv v) (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) p0024 p0027
  have p0029 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0030 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) p0029 p0030
  have p0032 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv r) (syn_chncodecmpset A)) p0031 p0032
  have p0034 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0035 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) p0034
  have p0036 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0037 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) p0036 p0037
  have p0039 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0038 p0039
  have p0041 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0035 p0040
  have p0042 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0033 p0041
  have p0043 :=
    @g_hncodecmpquotstrictbrproxyimpclndv A (.cv v) (.cv u) r dv_cache_0007 hyp_hnwcutstrictsegimp_1
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv v) (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (.cv v) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) p0042 p0043
  have p0045 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wbr (syn_cec (.cv v) (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (.cv v) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) p0028 p0044
  have p0046 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) hyp_hnwcutstrictsegimp_1
  have p0047 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0048 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) p0047
  have p0049 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0050 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
  have p0051 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) p0049 p0050
  have p0052 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0051 p0052
  have p0054 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0048 p0053
  have p0055 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0046 p0054
  have p0056 :=
    @g_hncodecmpstrictbrndv x u v A dv_cache_0005 dv_cache_0001 dv_cache_0002 dv_cache_0008 dv_cache_0009 dv_cache_0003
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))) (syn_wb (syn_wbr (.cv v) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))) p0055 p0056
  have p0058 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wbr (.cv v) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) p0045 p0057
  have p0059 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0060 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0061 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0062 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) p0060 p0061
  have p0063 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0064 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) p0063
  have p0065 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv v) (syn_chwcn A)) p0062 p0064
  have p0066 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0067 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) p0066 p0067
  have p0069 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0070 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) p0069 p0070
  have p0072 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0073 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0071 p0072
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv u) (syn_chwcn A)) p0068 p0073
  have p0075 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0076 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0077 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0075 p0076
  have p0078 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0074 p0077
  have p0079 :=
    @g_hnwcutcodeambientclndv u A (.cv x) dv_cache_0001
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0078 p0079
  have p0081 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0065 p0080
  have p0082 :=
    @g_hwnisoclasseqbcl A (.cv v) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) hyp_hnwcutstrictsegimp_1
  have p0083 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A))) (syn_wb (.classEq (syn_cec (.cv v) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) p0081 p0082
  have p0084 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classEq (syn_cec (.cv v) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) p0059 p0083
  have p0085 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_cec (.cv v) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) p0084
  have p0086 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0087 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0088 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) p0086 p0087
  have p0089 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0090 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) p0089
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) p0088 p0090
  have p0092 :=
    @g_eqtr4d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)) (.cv z) p0085 p0091
  have p0093 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)) p0092
  have p0094 :=
    @g_reximdva (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)) x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0010 p0093
  have p0095 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0058 p0094
  have p0096 :=
    @g_rexlimddv (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) v (syn_chwcn A) dv_cache_0011 dv_cache_0012 p0013 p0095
  have p0097 :=
    @g_ex (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0096
  have p0098 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))
  have p0099 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0100 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0101 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0099 p0100
  have p0102 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0103 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0101 p0102
  have p0104 :=
    @g_hnwcutcodeambientclndv u A (.cv x) dv_cache_0001
  have p0105 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0103 p0104
  have p0106 :=
    @g_hwnisoclasselhnordcl A (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) hyp_hnwcutstrictsegimp_1
  have p0107 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_chnord A)) p0105 p0106
  have p0108 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0109 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0110 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0108 p0109
  have p0111 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0112 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0110 p0111
  have p0113 :=
    @g_hnwcutcodeambientclndv u A (.cv x) dv_cache_0001
  have p0114 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0112 p0113
  have p0115 :=
    @g_elex (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)
  have p0116 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cvv)) p0114 p0115
  have p0117 :=
    @g_isset w (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) dv_cache_0013
  have p0118 :=
    @g_a1i (syn_wb (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cvv)) (syn_wex w (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0117
  have p0119 :=
    @g_mpbid (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cvv)) (syn_wex w (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) p0116 p0118
  have p0120 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0121 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0122 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0123 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0121 p0122
  have p0124 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0125 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0123 p0124
  have p0126 :=
    @g_hnwcutcodeambientclndv u A (.cv x) dv_cache_0001
  have p0127 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0125 p0126
  have p0128 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0120 p0127
  have p0129 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0130 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A) p0129
  have p0131 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classMem (.cv w) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0128 p0130
  have p0132 :=
    @g_hwnisorefli w A dv_cache_0014
  have p0133 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classMem (.cv w) (syn_chwcn A)) (syn_wbr (.cv w) (syn_chwniso A) (.cv w)) p0131 p0132
  have p0134 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0135 :=
    @g_breq2d (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv w) (syn_chwniso A) p0134
  have p0136 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wbr (.cv w) (syn_chwniso A) (.cv w)) (syn_wbr (.cv w) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) p0133 p0135
  have p0137 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0138 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0139 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0137 p0138
  have p0140 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classEq (.cv y) (.cv x))
  have p0141 :=
    @g_hnwcutcodeeq3 (.cv y) (.cv x) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0015
  have p0142 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classEq (.cv y) (.cv x))) (.classEq (.cv y) (.cv x)) (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) p0140 p0141
  have p0143 :=
    @g_breq2d (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classEq (.cv y) (.cv x))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv w) (syn_chwniso A) p0142
  have p0144 :=
    @g_rspcedv (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wbr (.cv w) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (syn_wbr (.cv w) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) y (.cv x) (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0139 p0143
  have p0145 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wbr (.cv w) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv w) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) p0136 p0144
  have p0146 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) hyp_hnwcutstrictsegimp_1
  have p0147 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0148 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0149 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0150 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0148 p0149
  have p0151 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0152 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0150 p0151
  have p0153 :=
    @g_hnwcutcodeambientclndv u A (.cv x) dv_cache_0001
  have p0154 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0152 p0153
  have p0155 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0147 p0154
  have p0156 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0157 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A) p0156
  have p0158 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classMem (.cv w) (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0155 p0157
  have p0159 :=
    @g_simpl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0160 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0161 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0162 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0160 p0161
  have p0163 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) p0159 p0162
  have p0164 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0158 p0163
  have p0165 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0146 p0164
  have p0166 :=
    @g_hncodecmpstrictbrndv y u w A dv_cache_0014 dv_cache_0001 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
  have p0167 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))) (syn_wb (syn_wbr (.cv w) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv w) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))) p0165 p0166
  have p0168 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wbr (.cv w) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv w) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) p0145 p0167
  have p0169 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0170 :=
    @g_breq1d (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) p0169
  have p0171 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))) (syn_wbr (.cv w) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) p0168 p0170
  have p0172 :=
    @g_exlimddv (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) w dv_cache_0024 dv_cache_0025 p0119 p0171
  have p0173 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0174 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0175 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv r) (syn_chncodecmpset A)) p0173 p0174
  have p0176 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0177 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0178 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0176 p0177
  have p0179 :=
    @g_simpr (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0180 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0178 p0179
  have p0181 :=
    @g_hnwcutcodeambientclndv u A (.cv x) dv_cache_0001
  have p0182 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) p0180 p0181
  have p0183 :=
    @g_simpl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0184 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0185 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0183 p0184
  have p0186 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0182 p0185
  have p0187 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0175 p0186
  have p0188 :=
    @g_hncodecmpquotstrictbrproxyimpclndv A (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (.cv u) r dv_cache_0007 hyp_hnwcutstrictsegimp_1
  have p0189 :=
    @g_syl (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) p0187 p0188
  have p0190 :=
    @g_mpbird (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) p0172 p0189
  have p0191 :=
    @g_eliniseg (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A))
  have p0192 :=
    @g_a1i (syn_wb (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_wbr (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A)))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0191
  have p0193 :=
    @g_mpbird (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_wbr (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec (.cv u) (syn_chwniso A))) p0190 p0192
  have p0194 :=
    @g_jca (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_chnord A)) (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) p0107 p0193
  have p0195 :=
    @g_elin (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))
  have p0196 :=
    @g_a1i (syn_wb (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wa (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_chnord A)) (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) p0195
  have p0197 :=
    @g_mpbird (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wa (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_chnord A)) (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0194 p0196
  have p0198 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0098 p0197
  have p0199 :=
    @g_simpr (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))
  have p0200 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) p0199
  have p0201 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classMem (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0198 p0200
  have p0202 :=
    @g_ex (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0201
  have p0203 :=
    @g_rexlimdva (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z)) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0026 dv_cache_0027 p0202
  have p0204 :=
    @g_impbid (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) p0097 p0203
  have p0205 :=
    @g_bitr4d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) (syn_chwniso A)) (.cv z))) (.classMem (.cv z) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0002 p0204
  have p0206 :=
    @g_eqrdv (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) z (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) dv_cache_0028 dv_cache_0029 dv_cache_0030 p0205
  exact p0206

#print axioms g_hnwcutambstrictsegranimpndv

end NFChoice.DirectNominalPrf.WPPReplay
