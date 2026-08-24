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
import NominalWPPReplayChunk015Compact001Part012

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

noncomputable def g_lnquounionb
    (u : Var) (C : Class) (R : Class) (S : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wb (.classMem (.cv u) (syn_cuni S)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ C.fv ∪ R.fv ∪ S.fv
  let b : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_u : b ≠ u := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_b : u ≠ b :=
    Ne.symm fresh_b_ne_u
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_S : w ∉ S.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_b_ne_w : b ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_b : w ≠ b :=
    Ne.symm fresh_b_ne_w
  have dv_cache_0001 : b ∉ ((Class.cv u)).fv := by
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ (S).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : Disjoint (C).fv ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (C).fv ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((C).fv) (({b} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show b ∉ (C).fv from (by exact fresh_b_not_C))))))
  have dv_cache_0004 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0005 : w ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : Disjoint ((Class.cv b)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint ((Class.cv b)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({b} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show b ∉ (R).fv from (by exact fresh_b_not_R))))))
  have dv_cache_0007 : w ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((Wff.classMem (syn_cec (.cv u) (syn_clnker R)) S)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_u, fresh_w_not_R, fresh_w_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_R, fresh_w_not_C, fresh_w_not_S, fresh_w_ne_u, fresh_w_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((Wff.classMem (syn_cec (.cv u) (syn_clnker R)) S)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_u, fresh_b_not_R, fresh_b_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, fresh_b_not_C, fresh_b_not_S, fresh_b_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))
  have p0001 :=
    @g_eluni2 b (.cv u) S dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_biimpi (.classMem (.cv u) (syn_cuni S)) (syn_wrex b S (.classMem (.cv u) (.cv b))) p0001
  have p0003 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (.classMem (.cv u) (syn_cuni S)) (syn_wrex b S (.classMem (.cv u) (.cv b))) p0000 p0002
  have p0004 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0005 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) p0004 p0005
  have p0007 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)
  have p0008 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (syn_wss S (syn_clnquo R C)) p0007 p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wss S (syn_clnquo R C)) p0006 p0009
  have p0011 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0012 :=
    @g_simpl (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))) (.classMem (.cv b) S) p0011 p0012
  have p0014 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) S (syn_clnquo R C) (.cv b) p0010 p0013
  have p0015 :=
    @g_vex b
  have p0016 :=
    @g_ellnquo w C (.cv b) R dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0015
  have p0017 :=
    @g_a1i (syn_wb (.classMem (.cv b) (syn_clnquo R C)) (syn_wrex w C (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) p0016
  have p0018 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (.classMem (.cv b) (syn_clnquo R C)) (syn_wrex w C (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))) p0014 p0017
  have p0019 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  have p0020 :=
    @g_simpr (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))) p0019 p0020
  have p0022 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  have p0023 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0024 :=
    @g_simpr (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))) (.classMem (.cv u) (.cv b)) p0023 p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (.classMem (.cv u) (.cv b)) p0022 p0025
  have p0027 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  have p0028 :=
    @g_simpr (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))) p0027 p0028
  have p0030 :=
    @g_eleq2d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (.cv b) (syn_cec (.cv w) (syn_clnker R)) (.cv u) p0029
  have p0031 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (.classMem (.cv u) (.cv b)) (.classMem (.cv u) (syn_cec (.cv w) (syn_clnker R))) p0026 p0030
  have p0032 :=
    @g_ellnkerecg (.cv u) (.cv w) R
  have p0033 :=
    @g_a1i (syn_wb (.classMem (.cv u) (syn_cec (.cv w) (syn_clnker R))) (syn_wa (syn_wbr (.cv w) R (.cv u)) (syn_wbr (.cv u) R (.cv w)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) p0032
  have p0034 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (.classMem (.cv u) (syn_cec (.cv w) (syn_clnker R))) (syn_wa (syn_wbr (.cv w) R (.cv u)) (syn_wbr (.cv u) R (.cv w))) p0031 p0033
  have p0035 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  have p0036 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0037 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) p0036 p0037
  have p0039 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) p0035 p0038
  have p0040 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)
  have p0041 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0040 p0041
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0039 p0042
  have p0044 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  have p0045 :=
    @g_simpl (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))) (.classMem (.cv w) C) p0044 p0045
  have p0047 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  have p0048 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0049 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))
  have p0050 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) p0048 p0049
  have p0051 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) p0047 p0050
  have p0052 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) C) p0051 p0052
  have p0054 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (.classMem (.cv w) C) (.classMem (.cv u) C) p0046 p0053
  have p0055 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem (.cv w) C) (.classMem (.cv u) C)) p0043 p0054
  have p0056 :=
    @g_lnkereceqb C R (.cv w) (.cv u) dv_cache_0004
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem (.cv w) C) (.classMem (.cv u) C))) (syn_wb (.classEq (syn_cec (.cv w) (syn_clnker R)) (syn_cec (.cv u) (syn_clnker R))) (syn_wa (syn_wbr (.cv w) R (.cv u)) (syn_wbr (.cv u) R (.cv w)))) p0055 p0056
  have p0058 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (.classEq (syn_cec (.cv w) (syn_clnker R)) (syn_cec (.cv u) (syn_clnker R))) (syn_wa (syn_wbr (.cv w) R (.cv u)) (syn_wbr (.cv u) R (.cv w))) p0034 p0057
  have p0059 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (.cv b) (syn_cec (.cv w) (syn_clnker R)) (syn_cec (.cv u) (syn_clnker R)) p0021 p0058
  have p0060 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  have p0061 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0062 :=
    @g_simpl (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))) (.classMem (.cv b) S) p0061 p0062
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (.classMem (.cv b) S) p0060 p0063
  have p0065 :=
    @g_eqeltrrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))) (.cv b) (syn_cec (.cv u) (syn_clnker R)) S p0059 p0064
  have p0066 :=
    @g_rexlimddv (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))) (.classMem (syn_cec (.cv u) (syn_clnker R)) S) w C dv_cache_0009 dv_cache_0010 p0018 p0065
  have p0067 :=
    @g_rexlimddv (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S))) (.classMem (.cv u) (.cv b)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S) b S dv_cache_0011 dv_cache_0012 p0003 p0066
  have p0068 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S) p0067
  have p0069 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)
  have p0070 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)
  have p0071 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))
  have p0072 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0070 p0071
  have p0073 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) p0072 p0073
  have p0075 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0076 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0074 p0075
  have p0077 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0078 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0076 p0077
  have p0079 :=
    @g_simpl (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cref) C) p0078 p0079
  have p0081 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wbr R (syn_cref) C) p0069 p0080
  have p0082 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)
  have p0083 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)
  have p0084 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) C) p0082 p0083
  have p0085 :=
    @g_refd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) C R (.cv u) p0081 p0084
  have p0086 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)
  have p0087 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)
  have p0088 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))
  have p0089 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0087 p0088
  have p0090 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) p0089 p0090
  have p0092 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0093 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0091 p0092
  have p0094 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0095 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0093 p0094
  have p0096 :=
    @g_simpl (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cref) C) p0095 p0096
  have p0098 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (syn_wbr R (syn_cref) C) p0086 p0097
  have p0099 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)
  have p0100 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)
  have p0101 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) C) p0099 p0100
  have p0102 :=
    @g_refd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) C R (.cv u) p0098 p0101
  have p0103 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) (syn_wbr (.cv u) R (.cv u)) (syn_wbr (.cv u) R (.cv u)) p0085 p0102
  have p0104 :=
    @g_ellnkerecg (.cv u) (.cv u) R
  have p0105 :=
    @g_a1i (syn_wb (.classMem (.cv u) (syn_cec (.cv u) (syn_clnker R))) (syn_wa (syn_wbr (.cv u) R (.cv u)) (syn_wbr (.cv u) R (.cv u)))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) p0104
  have p0106 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) (.classMem (.cv u) (syn_cec (.cv u) (syn_clnker R))) (syn_wa (syn_wbr (.cv u) R (.cv u)) (syn_wbr (.cv u) R (.cv u))) p0103 p0105
  have p0107 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)
  have p0108 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) (.classMem (.cv u) (syn_cec (.cv u) (syn_clnker R))) (.classMem (syn_cec (.cv u) (syn_clnker R)) S) p0106 p0107
  have p0109 :=
    @g_elunii (.cv u) (syn_cec (.cv u) (syn_clnker R)) S
  have p0110 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) (syn_wa (.classMem (.cv u) (syn_cec (.cv u) (syn_clnker R))) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)) (.classMem (.cv u) (syn_cuni S)) p0108 p0109
  have p0111 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S) (.classMem (.cv u) (syn_cuni S)) p0110
  have p0112 :=
    @g_impbid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C)) (.classMem (.cv u) (syn_cuni S)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S) p0068 p0111
  exact p0112

#print axioms g_lnquounionb

end NFChoice.DirectNominalPrf.WPPReplay
