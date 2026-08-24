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
import NominalWPPReplayChunk017Compact001Part074

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

noncomputable def g_hncodepw12repdndv
    (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) (hyp_hncodepw12repdndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  let t : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_v : t ≠ v := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_t : v ≠ t :=
    Ne.symm fresh_t_ne_v
  have fresh_t_ne_u : t ≠ u := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_ne_v : q ≠ v := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_q : v ≠ q :=
    Ne.symm fresh_q_ne_v
  have fresh_q_ne_u : q ≠ u := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_t_ne_q : t ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_t : q ≠ t :=
    Ne.symm fresh_t_ne_q
  have fresh_t_ne_z : t ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_q_ne_z : q ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_q : z ≠ q :=
    Ne.symm fresh_q_ne_z
  have dv_cache_0001 : t ∉ ((syn_cpw1 A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_u, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cuni (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_t, fresh_q_not_A, fresh_q_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cuni (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, fresh_z_not_A, fresh_z_ne_u, fresh_z_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show q ≠ z from (by exact fresh_q_ne_z))
  have dv_cache_0010 : v ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : v ∉ ((syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_v), fresh_v_ne_z, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Wff.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_u, fresh_z_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : q ∉ ((Wff.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_u, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : q ∉ ((syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_ne_u, fresh_q_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, fresh_t_ne_u, fresh_t_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((Wff.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_u, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pw1ex A hyp_hncodepw12repdndv_1
  have p0001 :=
    @g_pw1ex (syn_cpw1 A) p0000
  have p0002 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw1 A)) (.cv u) p0001
  have p0003 :=
    @g_id (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
  have p0004 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_chnord (syn_cpw1 (syn_cpw1 A))))) (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))) p0002 p0003
  have p0005 :=
    @g_pw1ex A hyp_hncodepw12repdndv_1
  have p0006 :=
    @g_hnsiquomappreexclndv t (syn_cpw1 A) (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) dv_cache_0001 dv_cache_0002 p0005
  have p0007 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_chnord (syn_cpw1 (syn_cpw1 A)))) (syn_wrex t (syn_cpw1 (syn_chnord (syn_cpw1 A))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) p0004 p0006
  have p0008 :=
    @g_simpl (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))
  have p0009 :=
    @g_pw1argclcl (syn_chnord (syn_cpw1 A)) (.cv t)
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (syn_wa (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A))) (.classEq (.cv t) (syn_csn (syn_cuni (.cv t))))) p0008 p0009
  have p0011 :=
    @g_simpl (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A))) (.classEq (.cv t) (syn_csn (syn_cuni (.cv t))))
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A))) (.classEq (.cv t) (syn_csn (syn_cuni (.cv t))))) (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A))) p0010 p0011
  have p0013 :=
    @g_hnsiquomappreexclndv q A (syn_cuni (.cv t)) dv_cache_0003 dv_cache_0004 hyp_hncodepw12repdndv_1
  have p0014 :=
    @g_syl (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A))) (syn_wrex q (syn_cpw1 (syn_chnord A)) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))) p0012 p0013
  have p0015 :=
    @g_nfv (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) q dv_cache_0005
  have p0016 :=
    @g_nfri (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) q p0015
  have p0017 :=
    @g_simpr (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
  have p0018 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
  have p0019 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0017 p0018
  have p0020 :=
    @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0019 p0020
  have p0022 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) p0021 p0022
  have p0024 :=
    @g_vex q
  have p0025 :=
    @g_uniex (.cv q) p0024
  have p0026 :=
    @g_elhnordclndv z A (syn_cuni (.cv q)) dv_cache_0006 dv_cache_0007
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_biimpi (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (syn_wrex z (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) p0027
  have p0029 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (syn_wrex z (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) p0023 p0028
  have p0030 :=
    @g_nfv (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) z dv_cache_0008
  have p0031 :=
    @g_nfri (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) z p0030
  have p0032 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0033 :=
    @g_simpl (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) (.classMem (.cv z) (syn_chwcn A)) p0032 p0033
  have p0035 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0036 :=
    @g_simpl (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
  have p0037 :=
    @g_simpr (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))
  have p0038 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))) p0036 p0037
  have p0039 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))) p0035 p0038
  have p0040 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0041 :=
    @g_simpl (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
  have p0042 :=
    @g_simpl (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) p0041 p0042
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) p0040 p0043
  have p0045 :=
    @g_hnsicodemapfndv A
  have p0046 :=
    @g_a1i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) p0045
  have p0047 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0048 :=
    @g_simpl (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
  have p0049 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) (.classMem (.cv z) (syn_chwcn A)) p0047 p0048
  have p0050 :=
    @g_snelpw1 (.cv z) (syn_chwcn A)
  have p0051 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (.cv z) (syn_chwcn A)) (.classMem (syn_csn (.cv z)) (syn_cpw1 (syn_chwcn A))) p0049 p0050
  have p0052 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (.cv z)) (syn_cpw1 (syn_chwcn A))) p0046 p0051
  have p0053 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv z)) (syn_chnsicodemap A)
  have p0054 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (.cv z)) (syn_cpw1 (syn_chwcn A)))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A))) p0052 p0053
  have p0055 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0056 :=
    @g_simpr (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
  have p0057 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
  have p0058 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) p0056 p0057
  have p0059 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) p0055 p0058
  have p0060 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0061 :=
    @g_simpr (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
  have p0062 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
  have p0063 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0061 p0062
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0060 p0063
  have p0065 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0066 :=
    @g_simpl (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
  have p0067 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) (.classMem (.cv z) (syn_chwcn A)) p0065 p0066
  have p0068 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0069 :=
    @g_simpr (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
  have p0070 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) p0068 p0069
  have p0071 :=
    @g_eqid (syn_cec (.cv z) (syn_chwniso A))
  have p0072 :=
    @g_a1i (.classEq (syn_cec (.cv z) (syn_chwniso A)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) p0071
  have p0073 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)) (syn_cec (.cv z) (syn_chwniso A)) p0070 p0072
  have p0074 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) p0067 p0073
  have p0075 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) p0064 p0074
  have p0076 :=
    @g_hnsiquomaprepvalndv z A q dv_cache_0003 dv_cache_0006 dv_cache_0009 hyp_hncodepw12repdndv_1
  have p0077 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwniso (syn_cpw1 A)))) p0075 p0076
  have p0078 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwniso (syn_cpw1 A))) p0059 p0077
  have p0079 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A))) (.classEq (syn_cuni (.cv t)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwniso (syn_cpw1 A)))) p0054 p0078
  have p0080 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (syn_wa (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A))) (.classEq (syn_cuni (.cv t)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwniso (syn_cpw1 A))))) p0044 p0079
  have p0081 :=
    @g_pw1ex A hyp_hncodepw12repdndv_1
  have p0082 :=
    @g_hnsiquomaprepvalcl2ndv (syn_cpw1 A) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) t dv_cache_0001 p0081
  have p0083 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (syn_wa (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A))) (.classEq (syn_cuni (.cv t)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwniso (syn_cpw1 A)))))) (.classEq (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))) p0080 p0082
  have p0084 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) p0039 p0083
  have p0085 :=
    @g_a1d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) p0003
  have p0086 :=
    @g_hnsicodemapfndv (syn_cpw1 A)
  have p0087 :=
    @g_a1i (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) p0086
  have p0088 :=
    @g_hnsicodemapfndv A
  have p0089 :=
    @g_a1i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) p0088
  have p0090 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0091 :=
    @g_simpl (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
  have p0092 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) (.classMem (.cv z) (syn_chwcn A)) p0090 p0091
  have p0093 :=
    @g_snelpw1 (.cv z) (syn_chwcn A)
  have p0094 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (.cv z) (syn_chwcn A)) (.classMem (syn_csn (.cv z)) (syn_cpw1 (syn_chwcn A))) p0092 p0093
  have p0095 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (.cv z)) (syn_cpw1 (syn_chwcn A))) p0089 p0094
  have p0096 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv z)) (syn_chnsicodemap A)
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (.cv z)) (syn_cpw1 (syn_chwcn A)))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A))) p0095 p0096
  have p0098 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A))
  have p0099 :=
    @g_sylibr (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))) p0097 p0098
  have p0100 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))) p0087 p0099
  have p0101 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))) (syn_chnsicodemap (syn_cpw1 A))
  have p0102 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))) (syn_cpw1 (syn_chwcn (syn_cpw1 A))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) p0100 p0101
  have p0103 :=
    @g_pm3_2 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
  have p0104 :=
    @g_syl5 (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))) p0102 p0103
  have p0105 :=
    @g_syl6 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))) p0085 p0104
  have p0106 :=
    @g_pm2_43d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))) p0105
  have p0107 :=
    @g_pw1ex A hyp_hncodepw12repdndv_1
  have p0108 :=
    @g_pw1ex (syn_cpw1 A) p0107
  have p0109 :=
    @g_hwnisoclasseqbcl (syn_cpw1 (syn_cpw1 A)) (.cv u) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) p0108
  have p0110 :=
    @g_syl6 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))) (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))) p0106 p0109
  have p0111 :=
    @g_bi1 (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))
  have p0112 :=
    @g_syl6 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))) (.imp (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))) p0110 p0111
  have p0113 :=
    @g_mpdi (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))) p0084 p0112
  have p0114 :=
    @g_pm3_2 (.classMem (.cv z) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))
  have p0115 :=
    @g_syl9 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))) (.classMem (.cv z) (syn_chwcn A)) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))) p0113 p0114
  have p0116 :=
    @g_syl5 (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (.classMem (.cv z) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))))) p0034 p0115
  have p0117 :=
    @g_pm2_43d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))) p0116
  have p0118 :=
    @g_id (.classEq (.cv v) (.cv z))
  have p0119 :=
    @g_sneqd (.classEq (.cv v) (.cv z)) (.cv v) (.cv z) p0118
  have p0120 :=
    @g_fveq2d (.classEq (.cv v) (.cv z)) (syn_csn (.cv v)) (syn_csn (.cv z)) (syn_chnsicodemap A) p0119
  have p0121 :=
    @g_sneqd (.classEq (.cv v) (.cv z)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) p0120
  have p0122 :=
    @g_fveq2d (.classEq (.cv v) (.cv z)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))) (syn_chnsicodemap (syn_cpw1 A)) p0121
  have p0123 :=
    @g_breq2d (.classEq (.cv v) (.cv z)) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))) (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) p0122
  have p0124 :=
    @g_rspcev (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))) v (.cv z) (syn_chwcn A) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0123
  have p0125 :=
    @g_syl6 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))) (syn_wa (.classMem (.cv z) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) p0117 p0124
  have p0126 :=
    @g_exp4d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.classMem (.cv z) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) p0125
  have p0127 :=
    @g_imp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.classMem (.cv z) (syn_chwcn A)) (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))) p0126
  have p0128 :=
    @g_exp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.classMem (.cv z) (syn_chwcn A)) (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))) p0127
  have p0129 :=
    @g_alimdv (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.imp (.classMem (.cv z) (syn_chwcn A)) (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) z dv_cache_0013 p0128
  have p0130 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.all z (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.all z (.imp (.classMem (.cv z) (syn_chwcn A)) (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))) p0031 p0129
  have p0131 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral z (syn_chwcn A) (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))))
  have p0132 :=
    @g_syl6ibr (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (.all z (.imp (.classMem (.cv z) (syn_chwcn A)) (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))) (syn_wral z (syn_chwcn A) (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) p0130 p0131
  have p0133 :=
    @g_nfv (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) z dv_cache_0014
  have p0134 :=
    @g_r19_23 (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) z (syn_chwcn A) p0133
  have p0135 :=
    @g_syl6ib (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wral z (syn_chwcn A) (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) (.imp (syn_wrex z (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))) p0132 p0134
  have p0136 :=
    @g_mpdi (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))) (syn_wrex z (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) p0029 p0135
  have p0137 :=
    @g_exp4d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) p0136
  have p0138 :=
    @g_imp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))) p0137
  have p0139 :=
    @g_exp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))) p0138
  have p0140 :=
    @g_alimdv (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) q dv_cache_0015 p0139
  have p0141 :=
    @g_syl5 (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.all q (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.all q (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))) p0016 p0140
  have p0142 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral q (syn_cpw1 (syn_chnord A)) (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))))
  have p0143 :=
    @g_syl6ibr (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (.all q (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))) (syn_wral q (syn_cpw1 (syn_chnord A)) (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) p0141 p0142
  have p0144 :=
    @g_nfv (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) q dv_cache_0016
  have p0145 :=
    @g_r19_23 (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) q (syn_cpw1 (syn_chnord A)) p0144
  have p0146 :=
    @g_syl6ib (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wral q (syn_cpw1 (syn_chnord A)) (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) (.imp (syn_wrex q (syn_cpw1 (syn_chnord A)) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))) p0143 p0145
  have p0147 :=
    @g_mpdi (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wrex q (syn_cpw1 (syn_chnord A)) (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) p0014 p0146
  have p0148 :=
    @g_exp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) p0147
  have p0149 :=
    @g_rexlimdv (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) t (syn_cpw1 (syn_chnord (syn_cpw1 A))) dv_cache_0017 dv_cache_0018 p0148
  have p0150 :=
    @g_mpd (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wrex t (syn_cpw1 (syn_chnord (syn_cpw1 A))) (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))) (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) p0007 p0149
  exact p0150

#print axioms g_hncodepw12repdndv

end NFChoice.DirectNominalPrf.WPPReplay
