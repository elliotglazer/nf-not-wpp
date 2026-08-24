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
import NominalWPPReplayChunk016Compact001Part034

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

noncomputable def g_wecutisoextendedterminaldfdv
    (x : Var) (y : Var) (u : Var) (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_u : u ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_E_y : y ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_h : h ∉ S.fv) (dv_S_u : u ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_h_u : h ≠ u) (dv_h_x : h ≠ x) (dv_h_y : h ≠ y) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (dv_x_y : x ≠ y) (hyp_wecutisoextendedterminaldfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisoextendedterminaldfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) (hyp_wecutisoextendedterminaldfdv_3 : Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({u} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({h} : Finset Var) ∪ E.fv
  let z : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_h : z ≠ h := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_z : h ≠ z :=
    Ne.symm fresh_z_ne_h
  have fresh_z_not_E : z ∉ E.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_ne_h : v ≠ h := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_v : h ≠ v :=
    Ne.symm fresh_v_ne_h
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_z_ne_v : z ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have dv_cache_0001 : z ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0004 : v ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0007 : h ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : h ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_E_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : h ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : u ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : h ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : u ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : h ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show h ≠ u from (by exact dv_h_u))
  have dv_cache_0024 : h ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show h ≠ x from (by exact dv_h_x))
  have dv_cache_0025 : h ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show h ≠ y from (by exact dv_h_y))
  have dv_cache_0026 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0027 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show u ≠ y from (by exact dv_u_y))
  have dv_cache_0028 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0029 : v ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : v ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : h ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0032 : v ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0033 : v ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0034 : v ∉ ((syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_D, fresh_v_not_E, fresh_v_not_R, fresh_v_ne_x, fresh_v_ne_h, fresh_v_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : v ∉ ((syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_y, fresh_v_not_D, fresh_v_ne_u, fresh_v_not_E, fresh_v_not_R, fresh_v_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : z ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : z ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : h ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (show h ≠ z from (by exact fresh_h_ne_z))
  have dv_cache_0039 : u ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0040 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0041 : v ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0042 : v ∉ ((syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_y, fresh_v_not_D, fresh_v_ne_u, fresh_v_not_E, fresh_v_not_R, fresh_v_not_S, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0043 : z ∉ ((syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_not_E, fresh_z_not_R, fresh_z_ne_x, fresh_z_ne_h, fresh_z_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0044 : z ∉ ((syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_D, fresh_z_ne_u, fresh_z_not_E, fresh_z_not_R, fresh_z_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpll (.classMem (.cv y) D) (.classMem (.cv u) E) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))
  have p0001 :=
    @g_weincsegcutorwholendv y z D R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wecutisoextendedterminaldfdv_1
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classMem (.cv y) D) (syn_wo (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (syn_wrex z D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))) p0000 p0001
  have p0003 :=
    @g_simplr (.classMem (.cv y) D) (.classMem (.cv u) E) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))
  have p0004 :=
    @g_weincsegcutorwholendv u v E S dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_wecutisoextendedterminaldfdv_2
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classMem (.cv u) E) (syn_wo (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) p0003 p0004
  have p0006 :=
    @g_a1d (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wo (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) p0005
  have p0007 :=
    @g_simprr (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))
  have p0008 :=
    @g_simprl (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))
  have p0009 :=
    @g_wecutisobranchwwknfdv x y u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 hyp_wecutisoextendedterminaldfdv_1 hyp_wecutisoextendedterminaldfdv_2 hyp_wecutisoextendedterminaldfdv_3
  have p0010 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.imp (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))) p0008 p0009
  have p0011 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0007 p0010
  have p0012 :=
    @g_exp3a (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0011
  have p0013 :=
    @g_imp (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.imp (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0012
  have p0014 :=
    @g_simprr (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))
  have p0015 :=
    @g_simprl (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))
  have p0016 :=
    @g_wecutisobranchwcknfdv x y v u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0029 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0030 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0005 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0031 dv_cache_0024 dv_cache_0025 dv_cache_0006 dv_cache_0026 dv_cache_0027 dv_cache_0032 dv_cache_0033 dv_cache_0028 hyp_wecutisoextendedterminaldfdv_1 hyp_wecutisoextendedterminaldfdv_2 hyp_wecutisoextendedterminaldfdv_3
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.imp (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))) p0015 p0016
  have p0018 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0014 p0017
  have p0019 :=
    @g_exp3a (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0018
  have p0020 :=
    @g_exp3a (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.classMem (.cv v) E) (.imp (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0019
  have p0021 :=
    @g_imp (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.imp (.classMem (.cv v) E) (.imp (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))) p0020
  have p0022 :=
    @g_imp (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D)) (.classMem (.cv v) E) (.imp (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0021
  have p0023 :=
    @g_rexlimdva (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D)) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) v E dv_cache_0034 dv_cache_0035 p0022
  have p0024 :=
    @g_jaod (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D)) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) p0013 p0023
  have p0025 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (.imp (syn_wo (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0024
  have p0026 :=
    @g_mpdd (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (syn_wo (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0006 p0025
  have p0027 :=
    @g_simplr (.classMem (.cv y) D) (.classMem (.cv u) E) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))
  have p0028 :=
    @g_weincsegcutorwholendv u v E S dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_wecutisoextendedterminaldfdv_2
  have p0029 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classMem (.cv u) E) (syn_wo (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) p0027 p0028
  have p0030 :=
    @g_a1d (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wo (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) p0029
  have p0031 :=
    @g_simprr (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))
  have p0032 :=
    @g_simprl (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))
  have p0033 :=
    @g_wecutisobranchcwknfdv x y z u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0036 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0002 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0037 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0038 dv_cache_0026 dv_cache_0027 dv_cache_0039 dv_cache_0028 dv_cache_0040 dv_cache_0003 hyp_wecutisoextendedterminaldfdv_1 hyp_wecutisoextendedterminaldfdv_2 hyp_wecutisoextendedterminaldfdv_3
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.imp (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))) p0032 p0033
  have p0035 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0031 p0034
  have p0036 :=
    @g_exp3a (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0035
  have p0037 :=
    @g_imp (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.imp (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0036
  have p0038 :=
    @g_simprr (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))
  have p0039 :=
    @g_simprl (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))))
  have p0040 :=
    @g_wecutisobranchccknfdv x y z v u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0029 dv_cache_0009 dv_cache_0010 dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0036 dv_cache_0015 dv_cache_0016 dv_cache_0030 dv_cache_0017 dv_cache_0018 dv_cache_0002 dv_cache_0019 dv_cache_0020 dv_cache_0005 dv_cache_0021 dv_cache_0022 dv_cache_0037 dv_cache_0023 dv_cache_0031 dv_cache_0024 dv_cache_0025 dv_cache_0038 dv_cache_0006 dv_cache_0026 dv_cache_0027 dv_cache_0039 dv_cache_0032 dv_cache_0033 dv_cache_0041 dv_cache_0028 dv_cache_0040 dv_cache_0003 hyp_wecutisoextendedterminaldfdv_1 hyp_wecutisoextendedterminaldfdv_2 hyp_wecutisoextendedterminaldfdv_3
  have p0041 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.imp (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))) p0039 p0040
  have p0042 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0038 p0041
  have p0043 :=
    @g_exp3a (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classMem (.cv v) E)) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0042
  have p0044 :=
    @g_exp3a (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classMem (.cv v) E) (.imp (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0043
  have p0045 :=
    @g_imp (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.imp (.classMem (.cv v) E) (.imp (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))) p0044
  have p0046 :=
    @g_imp (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))) (.classMem (.cv v) E) (.imp (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0045
  have p0047 :=
    @g_rexlimdva (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) v E dv_cache_0034 dv_cache_0042 p0046
  have p0048 :=
    @g_jaod (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))) (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))) p0037 p0047
  have p0049 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.imp (syn_wo (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0048
  have p0050 :=
    @g_mpdd (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (syn_wo (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0030 p0049
  have p0051 :=
    @g_exp3a (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0050
  have p0052 :=
    @g_imp (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classMem (.cv z) D) (.imp (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) p0051
  have p0053 :=
    @g_rexlimdva (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) z D dv_cache_0043 dv_cache_0044 p0052
  have p0054 :=
    @g_jaod (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) (syn_wrex z D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) p0026 p0053
  have p0055 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) (syn_csn (.cv u)))))) (syn_wo (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) D) (syn_wrex z D (.classEq (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_csn (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) p0002 p0054
  exact p0055

#print axioms g_wecutisoextendedterminaldfdv

end NFChoice.DirectNominalPrf.WPPReplay
