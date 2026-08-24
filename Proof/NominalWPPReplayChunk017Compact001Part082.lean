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
import NominalWPPReplayChunk017Compact001Part081

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

noncomputable def g_hnwcutambstrictsegresisomralias0ndv
    (u : Var) (A : Class) (r : Var) (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_r_u : r ≠ u) (hyp_hnwcutambstrictsegresisomralias0ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ ({r} : Finset Var)
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_p : u ≠ p :=
    Ne.symm fresh_p_ne_u
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_p : r ≠ p :=
    Ne.symm fresh_p_ne_r
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_ne_u : q ≠ u := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_r : q ≠ r := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ≠ u := by
    clear dv_cache_0001 dv_cache_0002
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0004 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0007 : p ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show p ≠ r from (by exact fresh_p_ne_r))
  have dv_cache_0008 : p ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show p ≠ u from (by exact fresh_p_ne_u))
  have dv_cache_0009 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0010 : q ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0011 : q ∉ ((syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_r, fresh_p_not_A, fresh_p_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_r, fresh_q_not_A, fresh_q_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : p ∉ ((syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_r, fresh_p_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : q ∉ ((syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_ne_r, fresh_q_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : q ∉ ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : p ∉ ((syn_clnqord (.cv r) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : q ∉ ((syn_clnqord (.cv r) (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0001 :=
    @g_hnwcutambfactorf1impndv u A dv_cache_0001 hyp_hnwcutambstrictsegresisomralias0ndv_1
  have p0002 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A)) p0000 p0001
  have p0003 :=
    @g_f1f1orn (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0004 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A)) (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))) p0002 p0003
  have p0005 :=
    @g_hnwcutambstrictsegranimpndv u A r dv_cache_0002 dv_cache_0001 dv_cache_0003 hyp_hnwcutambstrictsegresisomralias0ndv_1
  have p0006 :=
    @g_f1oeq3 (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0007 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (.classEq (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wb (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) p0005 p0006
  have p0008 :=
    @g_mpbid (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0004 p0007
  have p0009 :=
    @g_hnwcutambordbrproxyimpndv u A r q p dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0001 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0003 hyp_hnwcutambstrictsegresisomralias0ndv_1
  have p0010 :=
    @g_ralrimivva (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)))) p q (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0006 p0009
  have p0011 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wral p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wral q (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)))))) p0008 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso p q (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) dv_cache_0014 dv_cache_0011 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0006
  have p0013 :=
    @g_biimpri (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wa (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wral p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wral q (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q))))))) p0012
  have p0014 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wa (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wral p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wral q (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.cv q))))))) (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0011 p0013
  have p0015 :=
    @g_isores2 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0016 :=
    @g_a1i (syn_wb (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) p0015
  have p0017 :=
    @g_mpbid (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0014 p0016
  exact p0017

noncomputable def g_hnwcutambstrictsegresisomraliasdndv
    (u : Var) (A : Class) (r : Var) (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_r_u : r ≠ u) (hyp_hnwcutambstrictsegresisomraliasdndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (.cv r) (syn_chncodecmpset A)) (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ ({r} : Finset Var)
  have dv_cache_0001 : r ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ≠ u := by
    clear dv_cache_0001 dv_cache_0002
    exact (show r ≠ u from (by exact dv_r_u))
  have p0000 :=
    @g_hnwcutambstrictsegresisomralias0ndv u A r dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_hnwcutambstrictsegresisomraliasdndv_1
  have p0001 :=
    @g_ex (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)) (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))) (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) p0000
  exact p0001

#print axioms g_hnwcutambstrictsegresisomraliasdndv

end NFChoice.DirectNominalPrf.WPPReplay
