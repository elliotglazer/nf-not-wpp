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
import NominalWPPReplayChunk014Compact001Part055

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

noncomputable def g_ltfinsucle
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (.classMem (syn_copk B A) (syn_clefin)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cplc A (syn_c1c))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Wff.classMem (syn_copk B A) (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0001 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0002 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0003 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_elex B (syn_cnnc)
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0007 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0008 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) p0006 p0007
  have p0009 :=
    @g_peano2 A
  have p0010 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0008 p0009
  have p0011 :=
    @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0012 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0005 p0012
  have p0014 :=
    @g_opkltfing p B (syn_cplc A (syn_c1c)) (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002
  have p0015 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))) (syn_wb (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (syn_wa (syn_wne B (syn_c0)) (syn_wrex p (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))))) p0013 p0014
  have p0016 :=
    @g_biimpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (syn_wa (syn_wne B (syn_c0)) (syn_wrex p (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))) p0015
  have p0017 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (syn_wa (syn_wne B (syn_c0)) (syn_wrex p (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))) p0000 p0016
  have p0018 :=
    @g_simpr (syn_wne B (syn_c0)) (syn_wrex p (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
  have p0019 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (syn_wa (syn_wne B (syn_c0)) (syn_wrex p (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))) (syn_wrex p (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) p0017 p0018
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
  have p0021 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))
  have p0022 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0023 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0024 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) p0022 p0023
  have p0025 :=
    @g_elex B (syn_cnnc)
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0024 p0025
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem B (syn_cvv)) p0021 p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classMem B (syn_cvv)) p0020 p0027
  have p0029 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
  have p0030 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classMem (.cv p) (syn_cnnc)) p0029 p0030
  have p0032 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (.classMem B (syn_cvv)) (.classMem (.cv p) (syn_cnnc)) p0028 p0031
  have p0033 :=
    @g_lefinaddc B (.cv p) (syn_cvv)
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (syn_wa (.classMem B (syn_cvv)) (.classMem (.cv p) (syn_cnnc))) (.classMem (syn_copk B (syn_cplc B (.cv p))) (syn_clefin)) p0032 p0033
  have p0035 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
  have p0036 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
  have p0037 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))
  have p0038 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0039 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0040 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) p0038 p0039
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem A (syn_cnnc)) p0037 p0040
  have p0042 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))
  have p0043 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0044 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0045 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) p0043 p0044
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem B (syn_cnnc)) p0042 p0045
  have p0047 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))
  have p0048 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classMem B (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)) p0046 p0047
  have p0049 :=
    @g_nncaddccl B (.cv p)
  have p0050 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (syn_wa (.classMem B (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))) (.classMem (syn_cplc B (.cv p)) (syn_cnnc)) p0048 p0049
  have p0051 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classMem A (syn_cnnc)) (.classMem (syn_cplc B (.cv p)) (syn_cnnc)) p0041 p0050
  have p0052 :=
    @g_suc11nnc A (syn_cplc B (.cv p))
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (syn_wa (.classMem A (syn_cnnc)) (.classMem (syn_cplc B (.cv p)) (syn_cnnc))) (syn_wb (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))) (.classEq A (syn_cplc B (.cv p)))) p0051 p0052
  have p0054 :=
    @g_biimpd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))) (.classEq A (syn_cplc B (.cv p))) p0053
  have p0055 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.imp (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))) (.classEq A (syn_cplc B (.cv p)))) p0036 p0054
  have p0056 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))) (.classEq A (syn_cplc B (.cv p))) p0035 p0055
  have p0057 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) A (syn_cplc B (.cv p)) p0056
  have p0058 :=
    @g_opkeq2d (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (syn_cplc B (.cv p)) A B p0057
  have p0059 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (syn_copk B (syn_cplc B (.cv p))) (syn_copk B A) (syn_clefin) p0058
  have p0060 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (.classMem (syn_copk B (syn_cplc B (.cv p))) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)) p0034 p0059
  have p0061 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classMem (.cv p) (syn_cnnc))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))) (.classMem (syn_copk B A) (syn_clefin)) p0060
  have p0062 :=
    @g_rexlimdva (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))) (.classMem (syn_copk B A) (syn_clefin)) p (syn_cnnc) dv_cache_0003 dv_cache_0004 p0061
  have p0063 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))) (syn_wrex p (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))) (.classMem (syn_copk B A) (syn_clefin)) p0019 p0062
  have p0064 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (.classMem (syn_copk B A) (syn_clefin)) p0063
  exact p0064

noncomputable def g_lefinsucsplit
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wb (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
  have p0001 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
  have p0002 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0003 :=
    @g_elex B (syn_cnnc)
  have p0004 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0006 :=
    @g_peano2 A
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0005 p0006
  have p0008 :=
    @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0009 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0004 p0009
  have p0011 :=
    @g_lefinlteqall B (syn_cplc A (syn_c1c)) (syn_cvv) (syn_cvv)
  have p0012 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))) (syn_wb (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (.classEq B (syn_cplc A (syn_c1c))))) p0010 p0011
  have p0013 :=
    @g_biimpd (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (.classEq B (syn_cplc A (syn_c1c)))) p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (.classEq B (syn_cplc A (syn_c1c))))) p0001 p0013
  have p0015 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (.classEq B (syn_cplc A (syn_c1c)))) p0000 p0014
  have p0016 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
  have p0017 :=
    @g_ltfinsucle A B
  have p0018 :=
    @g_orc (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))
  have p0019 :=
    @g_syl6 (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (.classMem (syn_copk B A) (syn_clefin)) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))) p0017 p0018
  have p0020 :=
    @g_olc (.classEq B (syn_cplc A (syn_c1c))) (.classMem (syn_copk B A) (syn_clefin))
  have p0021 :=
    @g_a1i (.imp (.classEq B (syn_cplc A (syn_c1c))) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) p0020
  have p0022 :=
    @g_jaod (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))) (.classEq B (syn_cplc A (syn_c1c))) p0019 p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (.classEq B (syn_cplc A (syn_c1c)))) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))))) p0016 p0022
  have p0024 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))) (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)) (.classEq B (syn_cplc A (syn_c1c)))) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))) p0015 p0023
  have p0025 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))) p0024
  have p0026 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_clefin))
  have p0027 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_clefin))
  have p0028 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0029 :=
    @g_elex A (syn_cnnc)
  have p0030 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0028 p0029
  have p0031 :=
    @g_n_1cnnc
  have p0032 :=
    @g_a1i (.classMem (syn_c1c) (syn_cnnc)) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) p0031
  have p0033 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cvv)) (.classMem (syn_c1c) (syn_cnnc)) p0030 p0032
  have p0034 :=
    @g_lefinaddc A (syn_c1c) (syn_cvv)
  have p0035 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem A (syn_cvv)) (.classMem (syn_c1c) (syn_cnnc))) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin)) p0033 p0034
  have p0036 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_clefin))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin)) p0027 p0035
  have p0037 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_clefin))) (.classMem (syn_copk B A) (syn_clefin)) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin)) p0026 p0036
  have p0038 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_clefin))
  have p0039 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0040 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0041 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0042 :=
    @g_peano2 A
  have p0043 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0041 p0042
  have p0044 :=
    @g_n_3jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0039 p0040 p0043
  have p0045 :=
    @g_lefintrnn B A (syn_cplc A (syn_c1c))
  have p0046 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_w3a (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk B A) (syn_clefin)) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))) p0044 p0045
  have p0047 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_clefin))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk B A) (syn_clefin)) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))) p0038 p0046
  have p0048 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_clefin))) (syn_wa (.classMem (syn_copk B A) (syn_clefin)) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) p0037 p0047
  have p0049 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_clefin)) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) p0048
  have p0050 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq B (syn_cplc A (syn_c1c)))
  have p0051 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0052 :=
    @g_peano2 A
  have p0053 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0051 p0052
  have p0054 :=
    @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0055 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0053 p0054
  have p0056 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq B (syn_cplc A (syn_c1c)))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0050 p0055
  have p0057 :=
    @g_lefinrflx (syn_cplc A (syn_c1c)) (syn_cvv)
  have p0058 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq B (syn_cplc A (syn_c1c)))) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin)) p0056 p0057
  have p0059 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq B (syn_cplc A (syn_c1c)))
  have p0060 :=
    @g_opkeq1d (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq B (syn_cplc A (syn_c1c)))) B (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c)) p0059
  have p0061 :=
    @g_eleq1d (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq B (syn_cplc A (syn_c1c)))) (syn_copk B (syn_cplc A (syn_c1c))) (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin) p0060
  have p0062 :=
    @g_mpbird (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq B (syn_cplc A (syn_c1c)))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin)) p0058 p0061
  have p0063 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classEq B (syn_cplc A (syn_c1c))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) p0062
  have p0064 :=
    @g_jaod (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_clefin)) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))) p0049 p0063
  have p0065 :=
    @g_impbid (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))) p0025 p0064
  exact p0065

noncomputable def g_lefinzeroeq
    (B : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) (.classEq B (syn_c0c)))) := by
  let proofSupport : Finset Var := B.fv
  have p0000 :=
    @g_simpr (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
  have p0001 :=
    @g_simpl (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
  have p0002 :=
    @g_id (.classMem B (syn_cnnc))
  have p0003 :=
    @g_n_0cminle B
  have p0004 :=
    @g_syl (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem (syn_copk (syn_c0c) B) (syn_clefin)) p0002 p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))) (.classMem B (syn_cnnc)) (.classMem (syn_copk (syn_c0c) B) (syn_clefin)) p0001 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) (.classMem (syn_copk (syn_c0c) B) (syn_clefin)) p0000 p0005
  have p0007 :=
    @g_simpl (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
  have p0008 :=
    @g_id (.classMem B (syn_cnnc))
  have p0009 :=
    @g_peano1
  have p0010 :=
    @g_a1i (.classMem (syn_c0c) (syn_cnnc)) (.classMem B (syn_cnnc)) p0009
  have p0011 :=
    @g_jca (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc)) p0008 p0010
  have p0012 :=
    @g_syl (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))) (.classMem B (syn_cnnc)) (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc))) p0007 p0011
  have p0013 :=
    @g_lefinantinn B (syn_c0c)
  have p0014 :=
    @g_syl (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))) (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) (.classMem (syn_copk (syn_c0c) B) (syn_clefin))) (.classEq B (syn_c0c))) p0012 p0013
  have p0015 :=
    @g_mpd (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))) (syn_wa (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) (.classMem (syn_copk (syn_c0c) B) (syn_clefin))) (.classEq B (syn_c0c)) p0006 p0014
  have p0016 :=
    @g_ex (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) (.classEq B (syn_c0c)) p0015
  have p0017 :=
    @g_n_0cex
  have p0018 :=
    @g_lefinrflx (syn_c0c) (syn_cvv)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_a1i (.classMem (syn_copk (syn_c0c) (syn_c0c)) (syn_clefin)) (syn_wa (.classMem B (syn_cnnc)) (.classEq B (syn_c0c))) p0019
  have p0021 :=
    @g_simpr (.classMem B (syn_cnnc)) (.classEq B (syn_c0c))
  have p0022 :=
    @g_opkeq1d (syn_wa (.classMem B (syn_cnnc)) (.classEq B (syn_c0c))) B (syn_c0c) (syn_c0c) p0021
  have p0023 :=
    @g_eleq1d (syn_wa (.classMem B (syn_cnnc)) (.classEq B (syn_c0c))) (syn_copk B (syn_c0c)) (syn_copk (syn_c0c) (syn_c0c)) (syn_clefin) p0022
  have p0024 :=
    @g_mpbird (syn_wa (.classMem B (syn_cnnc)) (.classEq B (syn_c0c))) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) (.classMem (syn_copk (syn_c0c) (syn_c0c)) (syn_clefin)) p0020 p0023
  have p0025 :=
    @g_ex (.classMem B (syn_cnnc)) (.classEq B (syn_c0c)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) p0024
  have p0026 :=
    @g_impbid (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) (.classEq B (syn_c0c)) p0016 p0025
  exact p0026

noncomputable def g_kqfinsucsplit
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classEq B (syn_cplc A (syn_c1c)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0001 :=
    @g_elex B (syn_cnnc)
  have p0002 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0004 :=
    @g_peano2 A
  have p0005 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0003 p0004
  have p0006 :=
    @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0002 p0007
  have p0009 :=
    @g_kqlefinbr B (syn_cplc A (syn_c1c)) (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))) (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))) p0008 p0009
  have p0011 :=
    @g_lefinsucsplit A B
  have p0012 :=
    @g_bitrd (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))) p0010 p0011
  have p0013 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0014 :=
    @g_elex B (syn_cnnc)
  have p0015 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0017 :=
    @g_elex A (syn_cnnc)
  have p0018 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0016 p0017
  have p0019 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cvv)) (.classMem A (syn_cvv)) p0015 p0018
  have p0020 :=
    @g_kqlefinbr B A (syn_cvv) (syn_cvv)
  have p0021 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem B (syn_cvv)) (.classMem A (syn_cvv))) (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk B A) (syn_clefin))) p0019 p0020
  have p0022 :=
    @g_orbi1d (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))) p0021
  have p0023 :=
    @g_bitr4d (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))) (syn_wo (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classEq B (syn_cplc A (syn_c1c)))) p0012 p0022
  exact p0023

noncomputable def g_kqfinzeroeq
    (B : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classEq B (syn_c0c)))) := by
  let proofSupport : Finset Var := B.fv
  have p0000 :=
    @g_id (.classMem B (syn_cnnc))
  have p0001 :=
    @g_elex B (syn_cnnc)
  have p0002 :=
    @g_syl (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_n_0cex
  have p0004 :=
    @g_a1i (.classMem (syn_c0c) (syn_cvv)) (.classMem B (syn_cnnc)) p0003
  have p0005 :=
    @g_jca (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) (.classMem (syn_c0c) (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_kqlefinbr B (syn_c0c) (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_syl (.classMem B (syn_cnnc)) (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_c0c) (syn_cvv))) (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))) p0005 p0006
  have p0008 :=
    @g_lefinzeroeq B
  have p0009 :=
    @g_bitrd (.classMem B (syn_cnnc)) (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) (.classEq B (syn_c0c)) p0007 p0008
  exact p0009

noncomputable def g_kqfin0min
    (B : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) B)) := by
  let proofSupport : Finset Var := B.fv
  have p0000 :=
    @g_n_0cminle B
  have p0001 :=
    @g_n_0cex
  have p0002 :=
    @g_a1i (.classMem (syn_c0c) (syn_cvv)) (.classMem B (syn_cnnc)) p0001
  have p0003 :=
    @g_id (.classMem B (syn_cnnc))
  have p0004 :=
    @g_elex B (syn_cnnc)
  have p0005 :=
    @g_syl (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (.classMem B (syn_cnnc)) (.classMem (syn_c0c) (syn_cvv)) (.classMem B (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_kqlefinbr (syn_c0c) B (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl (.classMem B (syn_cnnc)) (syn_wa (.classMem (syn_c0c) (syn_cvv)) (.classMem B (syn_cvv))) (syn_wb (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) B) (.classMem (syn_copk (syn_c0c) B) (syn_clefin))) p0006 p0007
  have p0009 :=
    @g_mpbird (.classMem B (syn_cnnc)) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) B) (.classMem (syn_copk (syn_c0c) B) (syn_clefin)) p0000 p0008
  exact p0009

noncomputable def g_finleastbase
    (y : Var) (z : Var) (t : Var) (X : Class) (dv_X_t : t ∉ X.fv) (dv_X_y : y ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_t_y : t ≠ y) (dv_t_z : t ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (syn_wss X (syn_cnnc)) (.imp (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ({t} : Finset Var) ∪ X.fv
  have dv_cache_0001 : y ∉ ((syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_y, (Ne.symm dv_t_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (syn_c0c))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_y_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_wral y X (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_z, (Ne.symm dv_y_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_t, dv_t_z, dv_t_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_wss X (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))
  have p0001 :=
    @g_simpr (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (.classMem (.cv t) X) p0000 p0001
  have p0003 :=
    @g_simpr (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))
  have p0004 :=
    @g_simpl (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))
  have p0005 :=
    @g_simpl (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)
  have p0006 :=
    @g_simpr (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)
  have p0007 :=
    @g_sseldd (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) X (syn_cnnc) (.cv t) p0005 p0006
  have p0008 :=
    @g_kqfinzeroeq (.cv t)
  have p0009 :=
    @g_syl (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cnnc)) (syn_wb (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classEq (.cv t) (syn_c0c))) p0007 p0008
  have p0010 :=
    @g_biimpd (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classEq (.cv t) (syn_c0c)) p0009
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (.imp (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classEq (.cv t) (syn_c0c))) p0004 p0010
  have p0012 :=
    @g_mpd (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classEq (.cv t) (syn_c0c)) p0003 p0011
  have p0013 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.cv t) (syn_c0c) X p0012
  have p0014 :=
    @g_mpbid (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv t) X) (.classMem (syn_c0c) X) p0002 p0013
  have p0015 :=
    @g_simpl (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X)
  have p0016 :=
    @g_simpl (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))
  have p0017 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X)) (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) p0015 p0016
  have p0018 :=
    @g_simpl (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X)) (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wss X (syn_cnnc)) p0017 p0018
  have p0020 :=
    @g_simpr (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X)
  have p0021 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X)) X (syn_cnnc) (.cv y) p0019 p0020
  have p0022 :=
    @g_kqfin0min (.cv y)
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X)) (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y)) p0021 p0022
  have p0024 :=
    @g_ralrimiva (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y)) y X dv_cache_0001 p0023
  have p0025 :=
    @g_jca (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (syn_c0c) X) (syn_wral y X (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y))) p0014 p0024
  have p0026 :=
    @g_breq1 (.cv z) (syn_c0c) (.cv y) (syn_ckqrel (syn_clefin))
  have p0027 :=
    @g_ralbidv (.classEq (.cv z) (syn_c0c)) (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y)) y X dv_cache_0002 p0026
  have p0028 :=
    @g_rspcev (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wral y X (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y))) z (syn_c0c) X dv_cache_0003 dv_cache_0004 dv_cache_0005 p0027
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wa (.classMem (syn_c0c) X) (syn_wral y X (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y)))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0025 p0028
  have p0030 :=
    @g_ex (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0029
  have p0031 :=
    @g_rexlimdva (syn_wss X (syn_cnnc)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) t X dv_cache_0006 dv_cache_0007 p0030
  exact p0031

#print axioms g_finleastbase

end NFChoice.DirectNominalPrf.WPPReplay
