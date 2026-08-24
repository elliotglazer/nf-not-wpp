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
import NominalWPPReplayChunk013Compact001Part036

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

noncomputable def g_enmap2lem5
    (G : Class) (W : Class) (s : Var) (r : Var) (a : Var) (b : Var) (dv_G_s : s ∉ G.fv) (dv_a_s : a ≠ s) (dv_r_s : r ≠ s) (hyp_enmap2lem5_1 : Nominal.NPrf (.classEq W (syn_cmpt s (syn_co G (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf (.imp (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classEq (syn_crn W) (syn_co G (syn_cmap) (.cv b)))) := by
  let proofSupport : Finset Var := G.fv ∪ W.fv ∪ ({s} : Finset Var) ∪ ({r} : Finset Var) ∪ ({a} : Finset Var) ∪ ({b} : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_G : p ∉ G.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_p_not_W : p ∉ W.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_p_ne_s : p ≠ s := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_s_ne_p : s ≠ p :=
    Ne.symm fresh_p_ne_s
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_r_ne_p : r ≠ p :=
    Ne.symm fresh_p_ne_r
  have fresh_p_ne_a : p ≠ a := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_p : a ≠ p :=
    Ne.symm fresh_p_ne_a
  have fresh_p_ne_b : p ≠ b := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_p : b ≠ p :=
    Ne.symm fresh_p_ne_b
  have dv_cache_0001 : s ∉ (G).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ≠ s := by
    clear dv_cache_0001
    exact (show a ≠ s from (by exact dv_a_s))
  have dv_cache_0003 : s ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((syn_ccom (.cv p) (syn_ccnv (.cv r)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_p, (Ne.symm dv_r_s), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : s ∉ ((syn_co G (syn_cmap) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_s, (Ne.symm dv_a_s), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_wf1o (.cv r) (.cv a) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_a, fresh_p_ne_b, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_co G (syn_cmap) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_G, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_co G (syn_cmap) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_G, fresh_p_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ (W).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : s ∉ ((syn_ccom (.cv p) (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_p, (Ne.symm dv_r_s), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : s ∉ ((syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_p, (Ne.symm dv_r_s), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_crn W)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_enmap2lem2 G W s r a dv_cache_0001 dv_cache_0002 hyp_enmap2lem5_1
  have p0001 :=
    @g_coeq1 (.cv s) (.cv p) (syn_ccnv (.cv r))
  have p0002 :=
    @g_vex p
  have p0003 :=
    @g_vex r
  have p0004 :=
    @g_cnvex (.cv r) p0003
  have p0005 :=
    @g_coex (.cv p) (syn_ccnv (.cv r)) p0002 p0004
  have p0006 :=
    @g_fvmpt s (.cv p) (syn_ccom (.cv s) (syn_ccnv (.cv r))) (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv a)) W dv_cache_0003 dv_cache_0004 dv_cache_0005 p0001 hyp_enmap2lem5_1 p0005
  have p0007 :=
    @g_adantl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a))) (.classEq (syn_cfv W (.cv p)) (syn_ccom (.cv p) (syn_ccnv (.cv r)))) (syn_wf1o (.cv r) (.cv a) (.cv b)) p0006
  have p0008 :=
    @g_elmapi (.cv p) G (.cv a)
  have p0009 :=
    @g_f1ocnv (.cv a) (.cv b) (.cv r)
  have p0010 :=
    @g_f1of (.cv b) (.cv a) (syn_ccnv (.cv r))
  have p0011 :=
    @g_syl (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wf1o (syn_ccnv (.cv r)) (.cv b) (.cv a)) (syn_wf (syn_ccnv (.cv r)) (.cv b) (.cv a)) p0009 p0010
  have p0012 :=
    @g_fco (.cv b) (.cv a) G (.cv p) (syn_ccnv (.cv r))
  have p0013 :=
    @g_syl2anr (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a))) (syn_wf (.cv p) (.cv a) G) (syn_wf (syn_ccnv (.cv r)) (.cv b) (.cv a)) (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G) (syn_wf1o (.cv r) (.cv a) (.cv b)) p0008 p0011 p0012
  have p0014 :=
    @g_elovex1 (.cv p) G (.cv a) (syn_cmap)
  have p0015 :=
    @g_vex b
  have p0016 :=
    @g_elmapg G (.cv b) (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0017 :=
    @g_mp3an23 (.classMem G (syn_cvv)) (.classMem (.cv b) (syn_cvv)) (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_cvv)) (syn_wb (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv b))) (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G)) p0015 p0005 p0016
  have p0018 :=
    @g_syl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a))) (.classMem G (syn_cvv)) (syn_wb (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv b))) (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G)) p0014 p0017
  have p0019 :=
    @g_adantl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a))) (syn_wb (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv b))) (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G)) (syn_wf1o (.cv r) (.cv a) (.cv b)) p0018
  have p0020 :=
    @g_mpbird (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a)))) (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv b))) (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G) p0013 p0019
  have p0021 :=
    @g_eqeltrd (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a)))) (syn_cfv W (.cv p)) (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv b)) p0007 p0020
  have p0022 :=
    @g_ralrimiva (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (syn_cfv W (.cv p)) (syn_co G (syn_cmap) (.cv b))) p (syn_co G (syn_cmap) (.cv a)) dv_cache_0006 p0021
  have p0023 :=
    @g_fnfvrnss p (syn_co G (syn_cmap) (.cv a)) (syn_co G (syn_cmap) (.cv b)) W dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0024 :=
    @g_sylancr (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wfn W (syn_co G (syn_cmap) (.cv a))) (syn_wral p (syn_co G (syn_cmap) (.cv a)) (.classMem (syn_cfv W (.cv p)) (syn_co G (syn_cmap) (.cv b)))) (syn_wss (syn_crn W) (syn_co G (syn_cmap) (.cv b))) p0000 p0022 p0023
  have p0025 :=
    @g_elmapi (.cv p) G (.cv b)
  have p0026 :=
    @g_f1of (.cv a) (.cv b) (.cv r)
  have p0027 :=
    @g_fco (.cv a) (.cv b) G (.cv p) (.cv r)
  have p0028 :=
    @g_syl2anr (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))) (syn_wf (.cv p) (.cv b) G) (syn_wf (.cv r) (.cv a) (.cv b)) (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G) (syn_wf1o (.cv r) (.cv a) (.cv b)) p0025 p0026 p0027
  have p0029 :=
    @g_elovex1 (.cv p) G (.cv b) (syn_cmap)
  have p0030 :=
    @g_vex a
  have p0031 :=
    @g_coex (.cv p) (.cv r) p0002 p0003
  have p0032 :=
    @g_elmapg G (.cv a) (syn_ccom (.cv p) (.cv r)) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0033 :=
    @g_mp3an23 (.classMem G (syn_cvv)) (.classMem (.cv a) (syn_cvv)) (.classMem (syn_ccom (.cv p) (.cv r)) (syn_cvv)) (syn_wb (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a))) (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G)) p0030 p0031 p0032
  have p0034 :=
    @g_syl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))) (.classMem G (syn_cvv)) (syn_wb (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a))) (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G)) p0029 p0033
  have p0035 :=
    @g_adantl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))) (syn_wb (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a))) (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G)) (syn_wf1o (.cv r) (.cv a) (.cv b)) p0034
  have p0036 :=
    @g_mpbird (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b)))) (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a))) (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G) p0028 p0035
  have p0037 :=
    @g_coeq1 (.cv s) (syn_ccom (.cv p) (.cv r)) (syn_ccnv (.cv r))
  have p0038 :=
    @g_coass (.cv p) (.cv r) (syn_ccnv (.cv r))
  have p0039 :=
    @g_syl6eq (.classEq (.cv s) (syn_ccom (.cv p) (.cv r))) (syn_ccom (.cv s) (syn_ccnv (.cv r))) (syn_ccom (syn_ccom (.cv p) (.cv r)) (syn_ccnv (.cv r))) (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r)))) p0037 p0038
  have p0040 :=
    @g_coex (.cv r) (syn_ccnv (.cv r)) p0003 p0004
  have p0041 :=
    @g_coex (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r))) p0002 p0040
  have p0042 :=
    @g_fvmpt s (syn_ccom (.cv p) (.cv r)) (syn_ccom (.cv s) (syn_ccnv (.cv r))) (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r)))) (syn_co G (syn_cmap) (.cv a)) W dv_cache_0010 dv_cache_0011 dv_cache_0005 p0039 hyp_enmap2lem5_1 p0041
  have p0043 :=
    @g_syl (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b)))) (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a))) (.classEq (syn_cfv W (syn_ccom (.cv p) (.cv r))) (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r))))) p0036 p0042
  have p0044 :=
    @g_f1ococnv2 (.cv a) (.cv b) (.cv r)
  have p0045 :=
    @g_coeq2d (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_ccom (.cv r) (syn_ccnv (.cv r))) (syn_cres (syn_cid) (.cv b)) (.cv p) p0044
  have p0046 :=
    @g_fcoi1 (.cv b) G (.cv p)
  have p0047 :=
    @g_syl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))) (syn_wf (.cv p) (.cv b) G) (.classEq (syn_ccom (.cv p) (syn_cres (syn_cid) (.cv b))) (.cv p)) p0025 p0046
  have p0048 :=
    @g_sylan9eq (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))) (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r)))) (syn_ccom (.cv p) (syn_cres (syn_cid) (.cv b))) (.cv p) p0045 p0047
  have p0049 :=
    @g_eqtrd (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b)))) (syn_cfv W (syn_ccom (.cv p) (.cv r))) (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r)))) (.cv p) p0043 p0048
  have p0050 :=
    @g_fnbrfvb (syn_co G (syn_cmap) (.cv a)) (syn_ccom (.cv p) (.cv r)) (.cv p) W
  have p0051 :=
    @g_sylancr (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b)))) (syn_wfn W (syn_co G (syn_cmap) (.cv a))) (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a))) (syn_wb (.classEq (syn_cfv W (syn_ccom (.cv p) (.cv r))) (.cv p)) (syn_wbr (syn_ccom (.cv p) (.cv r)) W (.cv p))) p0000 p0036 p0050
  have p0052 :=
    @g_mpbid (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b)))) (.classEq (syn_cfv W (syn_ccom (.cv p) (.cv r))) (.cv p)) (syn_wbr (syn_ccom (.cv p) (.cv r)) W (.cv p)) p0049 p0051
  have p0053 :=
    @g_brelrn (syn_ccom (.cv p) (.cv r)) (.cv p) W
  have p0054 :=
    @g_syl (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b)))) (syn_wbr (syn_ccom (.cv p) (.cv r)) W (.cv p)) (.classMem (.cv p) (syn_crn W)) p0052 p0053
  have p0055 :=
    @g_ex (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))) (.classMem (.cv p) (syn_crn W)) p0054
  have p0056 :=
    @g_ssrdv (syn_wf1o (.cv r) (.cv a) (.cv b)) p (syn_co G (syn_cmap) (.cv b)) (syn_crn W) dv_cache_0008 dv_cache_0012 dv_cache_0006 p0055
  have p0057 :=
    @g_eqssd (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_crn W) (syn_co G (syn_cmap) (.cv b)) p0024 p0056
  exact p0057

noncomputable def g_enmap2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wbr A (syn_cen) B) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let s : Var := freshVar proofSupport 3
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_r : a ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_a : r ≠ a :=
    Ne.symm fresh_a_ne_r
  have fresh_a_ne_s : a ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_s_ne_a : s ≠ a :=
    Ne.symm fresh_a_ne_s
  have fresh_b_ne_r : b ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_b : r ≠ b :=
    Ne.symm fresh_b_ne_r
  have fresh_b_ne_s : b ≠ s := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_s_ne_b : s ≠ b :=
    Ne.symm fresh_b_ne_s
  have fresh_r_ne_s : r ≠ s := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_s_ne_r : s ≠ r :=
    Ne.symm fresh_r_ne_s
  have dv_cache_0001 : r ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : s ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ s from (by exact fresh_a_ne_s))
  have dv_cache_0005 : r ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ s from (by exact fresh_r_ne_s))
  have dv_cache_0006 : s ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, fresh_r_ne_a, fresh_r_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((Wff.imp (syn_wbr A (syn_cen) B) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B, fresh_b_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((Wff.imp (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, fresh_a_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex A B (syn_cen)
  have p0001 :=
    @g_breq1 (.cv a) A (.cv b) (syn_cen)
  have p0002 :=
    @g_oveq2 (.cv a) A C (syn_cmap)
  have p0003 :=
    @g_breq1d (.classEq (.cv a) A) (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) A) (syn_co C (syn_cmap) (.cv b)) (syn_cen) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv a) A) (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b))) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) (.cv b))) p0001 p0003
  have p0005 :=
    @g_breq2 (.cv b) B A (syn_cen)
  have p0006 :=
    @g_oveq2 (.cv b) B C (syn_cmap)
  have p0007 :=
    @g_breq2d (.classEq (.cv b) B) (syn_co C (syn_cmap) (.cv b)) (syn_co C (syn_cmap) B) (syn_co C (syn_cmap) A) (syn_cen) p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv b) B) (syn_wbr A (syn_cen) (.cv b)) (syn_wbr A (syn_cen) B) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) (.cv b))) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B)) p0005 p0007
  have p0009 :=
    @g_bren (.cv a) (.cv b) r dv_cache_0001 dv_cache_0002
  have p0010 :=
    @g_eqid (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
  have p0011 :=
    @g_enmap2lem4 C (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) s r a b dv_cache_0003 dv_cache_0004 dv_cache_0005 p0010
  have p0012 :=
    @g_dfrn4 (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
  have p0013 :=
    @g_enmap2lem5 C (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) s r a b dv_cache_0003 dv_cache_0004 dv_cache_0005 p0010
  have p0014 :=
    @g_syl5eqr (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_cdm (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) (syn_crn (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))) (syn_co C (syn_cmap) (.cv b)) p0012 p0013
  have p0015 :=
    @g_jca (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wfun (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) (.classEq (syn_cdm (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) (syn_co C (syn_cmap) (.cv b))) p0011 p0014
  have p0016 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))) (syn_co C (syn_cmap) (.cv b)))))
  have p0017 :=
    @g_sylibr (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wa (syn_wfun (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) (.classEq (syn_cdm (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) (syn_co C (syn_cmap) (.cv b)))) (syn_wfn (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))) (syn_co C (syn_cmap) (.cv b))) p0015 p0016
  have p0018 :=
    @g_enmap2lem2 C (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) s r a dv_cache_0003 dv_cache_0004 p0010
  have p0019 :=
    @g_dff1o4 (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b)) (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
  have p0020 :=
    @g_mpbiran (syn_wf1o (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b))) (syn_wfn (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) (syn_co C (syn_cmap) (.cv a))) (syn_wfn (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))) (syn_co C (syn_cmap) (.cv b))) p0018 p0019
  have p0021 :=
    @g_sylibr (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wfn (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))) (syn_co C (syn_cmap) (.cv b))) (syn_wf1o (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b))) p0017 p0020
  have p0022 :=
    @g_enmap2lem1 (.cv a) C (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) s r dv_cache_0006 dv_cache_0003 dv_cache_0005 p0010
  have p0023 :=
    @g_f1oen (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b)) (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) p0022
  have p0024 :=
    @g_syl (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wf1o (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b))) (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b))) p0021 p0023
  have p0025 :=
    @g_exlimiv (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b))) r dv_cache_0007 p0024
  have p0026 :=
    @g_sylbi (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wex r (syn_wf1o (.cv r) (.cv a) (.cv b))) (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b))) p0009 p0025
  have p0027 :=
    @g_vtocl2g (.imp (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b)))) (.imp (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) (.cv b)))) (.imp (syn_wbr A (syn_cen) B) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B))) a b A B (syn_cvv) (syn_cvv) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0004 p0008 p0026
  have p0028 :=
    @g_mpcom (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr A (syn_cen) B) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B)) p0000 p0027
  exact p0028

noncomputable def g_enpw1pw
    (A : Class) (hyp_enpw1pw_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cpw1 (syn_cpw A)) (syn_cen) (syn_cpw (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have dv_cache_0001 : x ∉ ((syn_cpw1fn)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cpw1fn)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cpw1 (syn_cpw A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cpw1 (syn_cpw A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cpw A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_wbr (.cv y) (syn_cpw1fn) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_cpw A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0013 : y ∉ ((syn_csn (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_wbr (syn_csn (.cv z)) (syn_cpw1fn) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cpw (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pw1fnf1o
  have p0001 :=
    @g_f1of1 (syn_c1c) (syn_cpw (syn_c1c)) (syn_cpw1fn)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_pw1ss1c (syn_cpw A)
  have p0004 :=
    @g_f1ores (syn_c1c) (syn_cpw (syn_c1c)) (syn_cpw1 (syn_cpw A)) (syn_cpw1fn)
  have p0005 :=
    @g_mp2an (syn_wf1 (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c))) (syn_wss (syn_cpw1 (syn_cpw A)) (syn_c1c)) (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) (syn_cpw1 (syn_cpw A)) (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw A)))) p0002 p0003 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y (syn_cpw1fn) (syn_cpw1 (syn_cpw A)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_elpw (.cv x) (syn_cpw1 A) p0007
  have p0009 :=
    @g_sspw1 z (.cv x) A dv_cache_0006 dv_cache_0007 p0007
  have p0010 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z))))))
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw z A dv_cache_0007
  have p0012 :=
    @g_eqabri (syn_wss (.cv z) A) z (syn_cpw A) p0011
  have p0013 :=
    @g_anbi1i (.classMem (.cv z) (syn_cpw A)) (syn_wss (.cv z) A) (.classEq (.cv x) (syn_cpw1 (.cv z))) p0012
  have p0014 :=
    @g_exbii (syn_wa (.classMem (.cv z) (syn_cpw A)) (.classEq (.cv x) (syn_cpw1 (.cv z)))) (syn_wa (syn_wss (.cv z) A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) z p0013
  have p0015 :=
    @g_bitr2i (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) (syn_wex z (syn_wa (.classMem (.cv z) (syn_cpw A)) (.classEq (.cv x) (syn_cpw1 (.cv z))))) (syn_wex z (syn_wa (syn_wss (.cv z) A) (.classEq (.cv x) (syn_cpw1 (.cv z))))) p0010 p0014
  have p0016 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cpw (syn_cpw1 A))) (syn_wss (.cv x) (syn_cpw1 A)) (syn_wex z (syn_wa (syn_wss (.cv z) A) (.classEq (.cv x) (syn_cpw1 (.cv z))))) (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) p0008 p0009 p0015
  have p0017 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))))
  have p0018 :=
    @g_elpw1 z (.cv y) (syn_cpw A) dv_cache_0008 dv_cache_0009
  have p0019 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw A))) (syn_wrex z (syn_cpw A) (.classEq (.cv y) (syn_csn (.cv z)))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)) p0018
  have p0020 :=
    @g_r19_41v (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)) z (syn_cpw A) dv_cache_0010
  have p0021 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw A))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))) (syn_wa (syn_wrex z (syn_cpw A) (.classEq (.cv y) (syn_csn (.cv z)))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))) (syn_wrex z (syn_cpw A) (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))) p0019 p0020
  have p0022 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw A))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))) (syn_wrex z (syn_cpw A) (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))) y p0021
  have p0023 :=
    @g_rexcom4 (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))) z y (syn_cpw A) dv_cache_0011 dv_cache_0012
  have p0024 :=
    @g_snex (.cv z)
  have p0025 :=
    @g_breq1 (.cv y) (syn_csn (.cv z)) (.cv x) (syn_cpw1fn)
  have p0026 :=
    @g_ceqsexv (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)) (syn_wbr (syn_csn (.cv z)) (syn_cpw1fn) (.cv x)) y (syn_csn (.cv z)) dv_cache_0013 dv_cache_0014 p0024 p0025
  have p0027 :=
    @g_vex z
  have p0028 :=
    @g_brpw1fn (.cv z) (.cv x) p0027
  have p0029 :=
    @g_bitri (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))) (syn_wbr (syn_csn (.cv z)) (syn_cpw1fn) (.cv x)) (.classEq (.cv x) (syn_cpw1 (.cv z))) p0026 p0028
  have p0030 :=
    @g_rexbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))) (.classEq (.cv x) (syn_cpw1 (.cv z))) z (syn_cpw A) p0029
  have p0031 :=
    @g_bitr3i (syn_wex y (syn_wrex z (syn_cpw A) (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))) (syn_wrex z (syn_cpw A) (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))) (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) p0023 p0030
  have p0032 :=
    @g_n_3bitri (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw A))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))) (syn_wex y (syn_wrex z (syn_cpw A) (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))) (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) p0017 p0022 p0031
  have p0033 :=
    @g_bitr4i (.classMem (.cv x) (syn_cpw (syn_cpw1 A))) (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))) p0016 p0032
  have p0034 :=
    @g_eqabi (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))) x (syn_cpw (syn_cpw1 A)) dv_cache_0015 p0033
  have p0035 :=
    @g_eqtr4i (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) (.cab x (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))) (syn_cpw (syn_cpw1 A)) p0006 p0034
  have p0036 :=
    @g_f1oeq3 (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) (syn_cpw (syn_cpw1 A)) (syn_cpw1 (syn_cpw A)) (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A)))
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_mpbi (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) (syn_cpw1 (syn_cpw A)) (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw A)))) (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) (syn_cpw1 (syn_cpw A)) (syn_cpw (syn_cpw1 A))) p0005 p0037
  have p0039 :=
    @g_pw1fnex
  have p0040 :=
    @g_pwex A hyp_enpw1pw_1
  have p0041 :=
    @g_pw1ex (syn_cpw A) p0040
  have p0042 :=
    @g_resex (syn_cpw1fn) (syn_cpw1 (syn_cpw A)) p0039 p0041
  have p0043 :=
    @g_f1oen (syn_cpw1 (syn_cpw A)) (syn_cpw (syn_cpw1 A)) (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) p0042
  have p0044 :=
    Nominal.mp p0038 p0043
  exact p0044

#print axioms g_enpw1pw

end NFChoice.DirectNominalPrf.WPPReplay
