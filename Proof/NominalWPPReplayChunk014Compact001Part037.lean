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
import NominalWPPReplayChunk014Compact001Part036

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

noncomputable def g_isotargettransport
    (A : Class) (B : Class) (S : Class) (f : Var) (r : Var) (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) (dv_S_f : f ∉ S.fv) (dv_f_r : f ≠ r) :
    Nominal.NPrf (.imp (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (.classEq S (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ S.fv ∪ ({f} : Finset Var) ∪ ({r} : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : f ≠ x := by
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0002 : f ≠ y := by
    clear dv_cache_0001
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0003 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_f, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_f, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_ne_f, fresh_x_ne_r, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_f, fresh_y_ne_r, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))
  have p0001 :=
    @g_ssbrd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) S (syn_cxp B B) (.cv x) (.cv y) p0000
  have p0002 :=
    @g_brxp (.cv x) (.cv y) B B
  have p0003 :=
    @g_a1i (syn_wb (syn_wbr (.cv x) (syn_cxp B B) (.cv y)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) p0002
  have p0004 :=
    @g_sylibd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cxp B B) (.cv y)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0001 p0003
  have p0005 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))
  have p0006 :=
    @g_ssbrd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) S (syn_cxp B B) (.cv x) (.cv y) p0005
  have p0007 :=
    @g_brxp (.cv x) (.cv y) B B
  have p0008 :=
    @g_a1i (syn_wb (syn_wbr (.cv x) (syn_cxp B B) (.cv y)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) p0007
  have p0009 :=
    @g_sylibd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cxp B B) (.cv y)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0006 p0008
  have p0010 :=
    @g_simpl (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))
  have p0011 :=
    @g_adantr (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wiso (.cv f) (.cv r) S A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0010
  have p0012 :=
    @g_simpr (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
  have p0013 :=
    @g_jca (syn_wa (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wiso (.cv f) (.cv r) S A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0011 p0012
  have p0014 :=
    @g_isocnv A B (.cv r) S (.cv f)
  have p0015 :=
    @g_anim1i (syn_wiso (.cv f) (.cv r) S A B) (syn_wiso (syn_ccnv (.cv f)) S (.cv r) B A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0014
  have p0016 :=
    @g_isorel B A (.cv x) (.cv y) S (.cv r) (syn_ccnv (.cv f))
  have p0017 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wa (syn_wiso (syn_ccnv (.cv f)) S (.cv r) B A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0015 p0016
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0013 p0017
  have p0019 :=
    @g_ex (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0018
  have p0020 :=
    @g_bi1 (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
  have p0021 :=
    @g_syl6 (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (.imp (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0019 p0020
  have p0022 :=
    @g_com23 (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) p0021
  have p0023 :=
    @g_mpdd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wbr (.cv x) S (.cv y)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) p0009 p0022
  have p0024 :=
    @g_jcad (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wbr (.cv x) S (.cv y)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) p0004 p0023
  have p0025 :=
    @g_simpl (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))
  have p0026 :=
    @g_adantr (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wiso (.cv f) (.cv r) S A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0025
  have p0027 :=
    @g_simpr (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
  have p0028 :=
    @g_jca (syn_wa (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wiso (.cv f) (.cv r) S A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0026 p0027
  have p0029 :=
    @g_isocnv A B (.cv r) S (.cv f)
  have p0030 :=
    @g_anim1i (syn_wiso (.cv f) (.cv r) S A B) (syn_wiso (syn_ccnv (.cv f)) S (.cv r) B A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0029
  have p0031 :=
    @g_isorel B A (.cv x) (.cv y) S (.cv r) (syn_ccnv (.cv f))
  have p0032 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wa (syn_wiso (syn_ccnv (.cv f)) S (.cv r) B A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0030 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))) (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0028 p0032
  have p0034 :=
    @g_ex (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0033
  have p0035 :=
    @g_bi2 (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
  have p0036 :=
    @g_syl6 (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (.imp (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (syn_wbr (.cv x) S (.cv y))) p0034 p0035
  have p0037 :=
    @g_imp3a (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (syn_wbr (.cv x) S (.cv y)) p0036
  have p0038 :=
    @g_impbid (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wbr (.cv x) S (.cv y)) (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0024 p0037
  have p0039 :=
    @g_simpl (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))
  have p0040 :=
    @g_isof1o A B (.cv r) S (.cv f)
  have p0041 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wiso (.cv f) (.cv r) S A B) (syn_wf1o (.cv f) A B) p0039 p0040
  have p0042 :=
    @g_f1ocnv A B (.cv f)
  have p0043 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wf1o (.cv f) A B) (syn_wf1o (syn_ccnv (.cv f)) B A) p0041 p0042
  have p0044 :=
    @g_f1ofun B A (syn_ccnv (.cv f))
  have p0045 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wf1o (syn_ccnv (.cv f)) B A) (syn_wfun (syn_ccnv (.cv f))) p0043 p0044
  have p0046 :=
    @g_hwtrnbrd x y f r dv_cache_0001 dv_cache_0002
  have p0047 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wfun (syn_ccnv (.cv f))) (syn_wb (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) p0045 p0046
  have p0048 :=
    @g_simpl (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))
  have p0049 :=
    @g_isof1o A B (.cv r) S (.cv f)
  have p0050 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wiso (.cv f) (.cv r) S A B) (syn_wf1o (.cv f) A B) p0048 p0049
  have p0051 :=
    @g_f1ofo A B (.cv f)
  have p0052 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wf1o (.cv f) A B) (syn_wfo (.cv f) A B) p0050 p0051
  have p0053 :=
    @g_forn A B (.cv f)
  have p0054 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wfo (.cv f) A B) (.classEq (syn_crn (.cv f)) B) p0052 p0053
  have p0055 :=
    @g_eleq2d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_crn (.cv f)) B (.cv x) p0054
  have p0056 :=
    @g_simpl (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))
  have p0057 :=
    @g_isof1o A B (.cv r) S (.cv f)
  have p0058 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wiso (.cv f) (.cv r) S A B) (syn_wf1o (.cv f) A B) p0056 p0057
  have p0059 :=
    @g_f1ofo A B (.cv f)
  have p0060 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wf1o (.cv f) A B) (syn_wfo (.cv f) A B) p0058 p0059
  have p0061 :=
    @g_forn A B (.cv f)
  have p0062 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wfo (.cv f) A B) (.classEq (syn_crn (.cv f)) B) p0060 p0061
  have p0063 :=
    @g_eleq2d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_crn (.cv f)) B (.cv y) p0062
  have p0064 :=
    @g_anbi12d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv x) B) (.classMem (.cv y) (syn_crn (.cv f))) (.classMem (.cv y) B) p0055 p0063
  have p0065 :=
    @g_anbi1d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) p0064
  have p0066 :=
    @g_bitrd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0047 p0065
  have p0067 :=
    @g_bitr4d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wbr (.cv x) S (.cv y)) (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) p0038 p0066
  have p0068 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) S (.cv y))))
  have p0069 :=
    @g_bicomi (syn_wbr (.cv x) S (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) S) p0068
  have p0070 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) S) (syn_wbr (.cv x) S (.cv y))) (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) p0069
  have p0071 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))))
  have p0072 :=
    @g_bicomi (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))) p0071
  have p0073 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))) (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) p0072
  have p0074 :=
    @g_n_3bitr4d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) S) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))) p0067 p0070 p0073
  have p0075 :=
    @g_eqrelrdv (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) x y S (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0074
  exact p0075

noncomputable def g_elhwnisogeniso
    (v : Var) (u : Var) (A : Class) (f : Var) (r : Var) (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u) (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wex f (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({f} : Finset Var) ∪ ({r} : Finset Var)
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0004 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0005 : f ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact dv_f_v))
  have dv_cache_0006 : r ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0007 : r ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show r ≠ v from (by exact dv_r_v))
  have dv_cache_0008 : r ∉ ((syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_f_r), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elhwnisogenf1o v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_r19_42v (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))) r (syn_cvv) dv_cache_0008
  have p0002 :=
    @g_bicomi (syn_wrex r (syn_cvv) (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) p0001
  have p0003 :=
    @g_hwtrnisob f r
  have p0004 :=
    @g_anbi1i (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))) p0003
  have p0005 :=
    @g_rexbii (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))) r (syn_cvv) p0004
  have p0006 :=
    @g_bitri (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wrex r (syn_cvv) (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) p0002 p0005
  have p0007 :=
    @g_exbii (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) f p0006
  have p0008 :=
    @g_anbi2i (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) (syn_wex f (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0007
  have p0009 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wex f (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))))) p0000 p0008
  exact p0009

noncomputable def g_hwcnraw
    (u : Var) (A : Class) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_elhwcn u A
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0000
  have p0002 :=
    @g_simpld (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0001
  exact p0002

noncomputable def g_hwcnsupp
    (u : Var) (A : Class) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_elhwcn u A
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0000
  have p0002 :=
    @g_simprd (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0001
  exact p0002

noncomputable def g_hwcnpair
    (u : Var) (A : Class) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_elhwcn u A
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0000
  have p0002 :=
    @g_simpld (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0001
  have p0003 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0004 :=
    @g_eleq2i (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (.cv u) p0003
  have p0005 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) p0004
  have p0006 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) p0002 p0005
  have p0007 :=
    @g_elin (.cv u) (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))
  have p0008 :=
    @g_biimpi (.classMem (.cv u) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (syn_wa (.classMem (.cv u) (syn_cwe)) (.classMem (.cv u) (syn_cxp (syn_cvv) (syn_cpw A)))) p0007
  have p0009 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (syn_wa (.classMem (.cv u) (syn_cwe)) (.classMem (.cv u) (syn_cxp (syn_cvv) (syn_cpw A)))) p0006 p0008
  have p0010 :=
    @g_simprd (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cwe)) (.classMem (.cv u) (syn_cxp (syn_cvv) (syn_cpw A))) p0009
  have p0011 :=
    @g_n_1st2nd2 (.cv u) (syn_cvv) (syn_cpw A)
  have p0012 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cxp (syn_cvv) (syn_cpw A))) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0010 p0011
  exact p0012

#print axioms g_hwcnpair

end NFChoice.DirectNominalPrf.WPPReplay
