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
import NominalWPPReplayChunk016Compact001Part048

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

noncomputable def g_wpphitminadjndv
    (k : Var) (m : Var) (n : Var) (F : Class) (H : Class) (I : Class) (L : Class) (r : Var) (q : Var) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_H_k : k ∉ H.fv) (dv_H_m : m ∉ H.fv) (dv_H_n : n ∉ H.fv) (dv_H_q : q ∉ H.fv) (dv_H_r : r ∉ H.fv) (dv_I_k : k ∉ I.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (dv_I_q : q ∉ I.fv) (dv_I_r : r ∉ I.fv) (dv_L_k : k ∉ L.fv) (dv_L_m : m ∉ L.fv) (dv_L_n : n ∉ L.fv) (dv_L_q : q ∉ L.fv) (dv_L_r : r ∉ L.fv) (dv_k_m : k ≠ m) (dv_k_n : k ≠ n) (dv_m_n : m ≠ n) (dv_n_q : n ≠ q) (dv_n_r : n ≠ r) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))) := by
  let proofSupport : Finset Var := ({k} : Finset Var) ∪ ({m} : Finset Var) ∪ ({n} : Finset Var) ∪ F.fv ∪ H.fv ∪ I.fv ∪ L.fv ∪ ({r} : Finset Var) ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_H_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_H_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ (I).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ (I).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show q ≠ n from (by exact Ne.symm dv_n_q))
  have dv_cache_0010 : r ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : r ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_H_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : r ∉ (I).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : r ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : r ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show r ≠ n from (by exact Ne.symm dv_n_r))
  have dv_cache_0015 : k ∉ ((syn_cwpphit F I H)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_H_k, dv_F_k, dv_I_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : m ∉ ((syn_cwpphit F I H)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_H_m, dv_F_m, dv_I_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : n ∉ ((syn_cwpphit F I H)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_H_n, dv_F_n, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : k ∉ ((syn_cwpphit F I L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_k, dv_F_k, dv_I_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : m ∉ ((syn_cwpphit F I L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_m, dv_F_m, dv_I_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : n ∉ ((syn_cwpphit F I L)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_L_n, dv_F_n, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : k ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show k ≠ m from (by exact dv_k_m))
  have dv_cache_0022 : k ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show k ≠ n from (by exact dv_k_n))
  have dv_cache_0023 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show m ≠ n from (by exact dv_m_n))
  have p0000 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
  have p0001 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
  have p0002 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))
  have p0004 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) p0002 p0003
  have p0005 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
  have p0006 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
  have p0007 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) p0005 p0006
  have p0008 :=
    @g_simpr (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))
  have p0009 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L))) p0007 p0008
  have p0010 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
  have p0011 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
  have p0012 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) p0010 p0011
  have p0013 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
  have p0014 :=
    @g_wpphitnestndv q n F H I L dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0015 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L)))) p0013 p0014
  have p0016 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
  have p0017 :=
    @g_simpl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))
  have p0018 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) p0016 p0017
  have p0019 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))
  have p0020 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) p0018 p0019
  have p0021 :=
    @g_simp3 (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))
  have p0022 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r)))))) p0020 p0021
  have p0023 :=
    @g_wpphitstepndv r n F H I L dv_cache_0010 dv_cache_0002 dv_cache_0011 dv_cache_0004 dv_cache_0012 dv_cache_0006 dv_cache_0013 dv_cache_0008 dv_cache_0014
  have p0024 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H)))) p0022 p0023
  have p0025 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H)))) p0015 p0024
  have p0026 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H))))) p0012 p0025
  have p0027 :=
    @g_n_3jca (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L))) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H)))))) p0004 p0009 p0026
  have p0028 :=
    @g_finleastadjndv k m n (syn_cwpphit F I H) (syn_cwpphit F I L) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
  have p0029 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L)))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs)) (syn_wbr L (syn_clec) H))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) (.cv r))) (syn_wbr H (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) (.cv r))))))) (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit F I H)) (.classMem (.cv k) (syn_cwpphit F I L))) (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I H)) (.classMem (.cv n) (syn_cwpphit F I L)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I L)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cwpphit F I H))))))) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) p0027 p0028
  exact p0029

noncomputable def g_wppcardt2fnexndv
     :
    Nominal.NPrf (.classMem (syn_cwppcardt2fn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwppcardt2fn] using (Nominal.classEqRefl (syn_cwppcardt2fn)))
  have p0001 :=
    @g_wppcardtfnexndv
  have p0002 :=
    @g_wppcardtfnexndv
  have p0003 :=
    @g_siex (syn_cwppcardtfn) p0002
  have p0004 :=
    @g_coex (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)) p0001 p0003
  have p0005 :=
    @g_eqeltri (syn_cwppcardt2fn) (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) (syn_cvv) p0000 p0004
  exact p0005

noncomputable def g_wppcardt2fnmapndv
     :
    Nominal.NPrf (syn_wf (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_wppcardtfnmapndv
  have p0001 :=
    @g_wppcardtfnmapndv
  have p0002 :=
    @g_sifmap (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_pm3_2i (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) (syn_wf (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs))) p0000 p0003
  have p0005 :=
    @g_fco (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    (by simpa [syn_cwppcardt2fn] using (Nominal.classEqRefl (syn_cwppcardt2fn)))
  have p0008 :=
    @g_feq1i (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) p0007
  have p0009 :=
    @g_mpbir (syn_wf (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) p0006 p0008
  exact p0009

noncomputable def g_wppcardt2fnvalsingndv
    (D : Class) :
    Nominal.NPrf (.imp (.classMem D (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))) (syn_ctc (syn_ctc D)))) := by
  let proofSupport : Finset Var := D.fv
  have p0000 :=
    (by simpa [syn_cwppcardt2fn] using (Nominal.classEqRefl (syn_cwppcardt2fn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn D)) (syn_cwppcardt2fn) (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))) (syn_cfv (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) (syn_csn (syn_csn D)))) (.classMem D (syn_cncs)) p0001
  have p0003 :=
    @g_wppcardtfnmapndv
  have p0004 :=
    @g_sifmap (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_a1i (syn_wf (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0005
  have p0007 :=
    @g_snelpw1 D (syn_cncs)
  have p0008 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0007
  have p0009 :=
    @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0010 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0009
  have p0011 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0008 p0010
  have p0012 :=
    @g_jca (.classMem D (syn_cncs)) (syn_wf (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0006 p0011
  have p0013 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs)) (syn_csn (syn_csn D)) (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))
  have p0014 :=
    @g_syl (.classMem D (syn_cncs)) (syn_wa (syn_wf (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classEq (syn_cfv (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) (syn_csn (syn_csn D))) (syn_cfv (syn_cwppcardtfn) (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D))))) p0012 p0013
  have p0015 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))) (syn_cfv (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))) (syn_csn (syn_csn D))) (syn_cfv (syn_cwppcardtfn) (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D)))) p0002 p0014
  have p0016 :=
    @g_snelpw1 D (syn_cncs)
  have p0017 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0016
  have p0018 :=
    @g_wppcardtfnmapndv
  have p0019 :=
    @g_sifvald (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_csn D) (syn_cwppcardtfn) p0018
  have p0020 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D))) (syn_csn (syn_cfv (syn_cwppcardtfn) (syn_csn D)))) p0017 p0019
  have p0021 :=
    @g_wppcardtfnvalsingndv D
  have p0022 :=
    @g_sneqd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardtfn) (syn_csn D)) (syn_ctc D) p0021
  have p0023 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D))) (syn_csn (syn_cfv (syn_cwppcardtfn) (syn_csn D))) (syn_csn (syn_ctc D)) p0020 p0022
  have p0024 :=
    @g_fveq2d (.classMem D (syn_cncs)) (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D))) (syn_csn (syn_ctc D)) (syn_cwppcardtfn) p0023
  have p0025 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))) (syn_cfv (syn_cwppcardtfn) (syn_cfv (syn_csi (syn_cwppcardtfn)) (syn_csn (syn_csn D)))) (syn_cfv (syn_cwppcardtfn) (syn_csn (syn_ctc D))) p0015 p0024
  have p0026 :=
    @g_tccl D
  have p0027 :=
    @g_wppcardtfnvalsingndv (syn_ctc D)
  have p0028 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc D) (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardtfn) (syn_csn (syn_ctc D))) (syn_ctc (syn_ctc D))) p0026 p0027
  have p0029 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))) (syn_cfv (syn_cwppcardtfn) (syn_csn (syn_ctc D))) (syn_ctc (syn_ctc D)) p0025 p0028
  exact p0029

noncomputable def g_hwgenvalclndv
    (B : Class) (C : Class) (hyp_hwgenvalclndv_1 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_hwgenvalclndv_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chwgen) (syn_cop B C)) (syn_cop (syn_cop C (syn_cdm B)) (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B)))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Wff.classEq (syn_cfv (syn_chwgen) (syn_cop B C)) (syn_cop (syn_cop C (syn_cdm B)) (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_B, fresh_f_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv f) B)
  have p0001 :=
    @g_opeq1d (.classEq (.cv f) B) (.cv f) B C p0000
  have p0002 :=
    @g_fveq2d (.classEq (.cv f) B) (syn_cop (.cv f) C) (syn_cop B C) (syn_chwgen) p0001
  have p0003 :=
    @g_id (.classEq (.cv f) B)
  have p0004 :=
    @g_dmeqd (.classEq (.cv f) B) (.cv f) B p0003
  have p0005 :=
    @g_opeq2d (.classEq (.cv f) B) (syn_cdm (.cv f)) (syn_cdm B) C p0004
  have p0006 :=
    @g_id (.classEq (.cv f) B)
  have p0007 :=
    @g_coeq1d (.classEq (.cv f) B) (.cv f) B C p0006
  have p0008 :=
    @g_id (.classEq (.cv f) B)
  have p0009 :=
    @g_cnveqd (.classEq (.cv f) B) (.cv f) B p0008
  have p0010 :=
    @g_coeq12d (.classEq (.cv f) B) (syn_ccom (.cv f) C) (syn_ccom B C) (syn_ccnv (.cv f)) (syn_ccnv B) p0007 p0009
  have p0011 :=
    @g_id (.classEq (.cv f) B)
  have p0012 :=
    @g_rneqd (.classEq (.cv f) B) (.cv f) B p0011
  have p0013 :=
    @g_opeq12d (.classEq (.cv f) B) (syn_ccom (syn_ccom (.cv f) C) (syn_ccnv (.cv f))) (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn (.cv f)) (syn_crn B) p0010 p0012
  have p0014 :=
    @g_opeq12d (.classEq (.cv f) B) (syn_cop C (syn_cdm (.cv f))) (syn_cop C (syn_cdm B)) (syn_cop (syn_ccom (syn_ccom (.cv f) C) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B)) p0005 p0013
  have p0015 :=
    @g_eqeq12d (.classEq (.cv f) B) (syn_cfv (syn_chwgen) (syn_cop (.cv f) C)) (syn_cfv (syn_chwgen) (syn_cop B C)) (syn_cop (syn_cop C (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) C) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) (syn_cop (syn_cop C (syn_cdm B)) (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B))) p0002 p0014
  have p0016 :=
    @g_hwgenval C f hyp_hwgenvalclndv_2
  have p0017 :=
    @g_vtoclg (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) C)) (syn_cop (syn_cop C (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) C) (syn_ccnv (.cv f))) (syn_crn (.cv f))))) (.classEq (syn_cfv (syn_chwgen) (syn_cop B C)) (syn_cop (syn_cop C (syn_cdm B)) (syn_cop (syn_ccom (syn_ccom B C) (syn_ccnv B)) (syn_crn B)))) f B (syn_cvv) dv_cache_0001 dv_cache_0002 p0015 p0016
  have p0018 :=
    Nominal.mp hyp_hwgenvalclndv_1 p0017
  exact p0018

noncomputable def g_hnbaseresfnvalndv
    (u : Var) (F : Class) (hyp_hnbaseresfnvalndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hnbaseresfnvalndv_2 : Nominal.NPrf (.classMem (.cv u) (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chnbaseresfn F) (.cv u)) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ F.fv
  have p0000 :=
    (by simpa [syn_chnbaseresfn] using (Nominal.classEqRefl (syn_chnbaseresfn F)))
  have p0001 :=
    @g_fveq1i (.cv u) (syn_chnbaseresfn F) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) p0000
  have p0002 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0003 :=
    Nominal.mp hyp_hnbaseresfnvalndv_1 p0002
  have p0004 :=
    @g_ln2ndfn
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_inidm (syn_cvv)
  have p0009 :=
    @g_eqcomi (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) p0008
  have p0010 :=
    @g_fneq2i (syn_cvv) (syn_cin (syn_cvv) (syn_cvv)) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) p0009
  have p0011 :=
    @g_mpbir (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cvv)) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) p0007 p0010
  have p0012 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0011 hyp_hnbaseresfnvalndv_2
  have p0013 :=
    @g_fvco2 (syn_cvv) (.cv u) (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0016 :=
    Nominal.mp hyp_hnbaseresfnvalndv_1 p0015
  have p0017 :=
    @g_ln2ndfn
  have p0018 :=
    @g_fvtxpvv (.cv u) (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd) p0016 p0017 hyp_hnbaseresfnvalndv_2
  have p0019 :=
    @g_fvconst2 (syn_cvv) F (.cv u) hyp_hnbaseresfnvalndv_1
  have p0020 :=
    Nominal.mp hyp_hnbaseresfnvalndv_2 p0019
  have p0021 :=
    @g_eqid (syn_cfv (syn_c2nd) (.cv u))
  have p0022 :=
    @g_opeq12i (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) (.cv u)) F (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) p0020 p0021
  have p0023 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (.cv u)) (syn_cop (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cop F (syn_cfv (syn_c2nd) (.cv u))) p0018 p0022
  have p0024 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (.cv u)) (syn_cop F (syn_cfv (syn_c2nd) (.cv u))) (syn_clnimageresfn) p0023
  have p0025 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (.cv u)) (syn_cfv (syn_clnimageresfn) (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (.cv u))) (syn_cfv (syn_clnimageresfn) (syn_cop F (syn_cfv (syn_c2nd) (.cv u)))) p0014 p0024
  have p0026 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0027 :=
    @g_lnimageresfnval (syn_cfv (syn_c2nd) (.cv u)) F hyp_hnbaseresfnvalndv_1 p0026
  have p0028 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (.cv u)) (syn_cfv (syn_clnimageresfn) (syn_cop F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0025 p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_chnbaseresfn F) (.cv u)) (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (.cv u)) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0001 p0028
  exact p0029

#print axioms g_hnbaseresfnvalndv

end NFChoice.DirectNominalPrf.WPPReplay
