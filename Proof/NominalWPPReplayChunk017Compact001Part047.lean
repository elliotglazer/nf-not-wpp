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
import NominalWPPReplayChunk017Compact001Part046

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

noncomputable def g_hncodecmpstrictminndv
    (y : Var) (u : Var) (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_q_u : q ≠ u) (dv_q_y : q ≠ y) (dv_u_y : u ≠ y) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u)))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({q} : Finset Var)
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_q : v ≠ q := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_v : q ≠ v :=
    Ne.symm fresh_v_ne_q
  have dv_cache_0001 : v ∉ ((Class.cv q)).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_q_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv u) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_y), fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_q_u), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv v))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_q_u), dv_u_y, fresh_u_ne_v, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0012 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show u ≠ y from (by exact dv_u_y))
  have dv_cache_0013 : v ∉ ((syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_q, fresh_v_ne_y, fresh_v_ne_u, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : v ∉ ((syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, fresh_v_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))
  have p0001 :=
    @g_simprd (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)) p0000
  have p0002 :=
    @g_n0 v (.cv q) dv_cache_0001
  have p0003 :=
    @g_biimpi (syn_wne (.cv q) (syn_c0)) (syn_wex v (.classMem (.cv v) (.cv q))) p0002
  have p0004 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (syn_wne (.cv q) (syn_c0)) (syn_wex v (.classMem (.cv v) (.cv q))) p0001 p0003
  have p0005 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0006 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classMem (.cv v) (.cv q)) p0005 p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0009 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))
  have p0010 :=
    @g_simpl (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))
  have p0011 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem A (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classMem A (syn_cvv)) p0008 p0011
  have p0013 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0014 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))
  have p0015 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))
  have p0016 :=
    @g_simpld (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)) p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (syn_wss (.cv q) (syn_chwcn A)) p0014 p0016
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wss (.cv q) (syn_chwcn A)) p0013 p0017
  have p0019 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0020 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classMem (.cv v) (.cv q)) p0019 p0020
  have p0022 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q)) p0018 p0021
  have p0023 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q))) p0012 p0022
  have p0024 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0025 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q)))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_hncodepredemptyminimalndv y v A (.cv q) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q)))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv v)))) p0025 p0026
  have p0028 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (.classMem (.cv v) (.cv q)) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv v)))) p0007 p0027
  have p0029 :=
    @g_breq2 (.cv u) (.cv v) (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
  have p0030 :=
    @g_eqeq2 (.cv u) (.cv v) (.cv y)
  have p0031 :=
    @g_imbi12d (.classEq (.cv u) (.cv v)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv u)) (.classEq (.cv y) (.cv v)) p0029 p0030
  have p0032 :=
    @g_ralbidv (.classEq (.cv u) (.cv v)) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u))) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv v))) y (.cv q) dv_cache_0006 p0031
  have p0033 :=
    @g_rspcev (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u)))) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv v)))) u (.cv v) (.cv q) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0032
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (.classMem (.cv v) (.cv q)) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv v))))) (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u))))) p0028 p0033
  have p0035 :=
    @g_ex (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classEq (syn_chncodepredends A (.cv q) v) (syn_c0)) (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u))))) p0034
  have p0036 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0037 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))
  have p0038 :=
    @g_simpl (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))
  have p0039 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem A (syn_cvv)) p0037 p0038
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classMem A (syn_cvv)) p0036 p0039
  have p0041 :=
    @g_vex q
  have p0042 :=
    @g_a1i (.classMem (.cv q) (syn_cvv)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) p0041
  have p0043 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) (.classMem A (syn_cvv)) (.classMem (.cv q) (syn_cvv)) p0040 p0042
  have p0044 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0045 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))
  have p0046 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))
  have p0047 :=
    @g_simpld (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)) p0046
  have p0048 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (syn_wss (.cv q) (syn_chwcn A)) p0045 p0047
  have p0049 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wss (.cv q) (syn_chwcn A)) p0044 p0048
  have p0050 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0051 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))
  have p0052 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (.classMem (.cv v) (.cv q)) p0050 p0051
  have p0053 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q)) p0049 p0052
  have p0054 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (.classMem A (syn_cvv)) (.classMem (.cv q) (syn_cvv))) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q))) p0043 p0053
  have p0055 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))
  have p0056 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem (.cv q) (syn_cvv))) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q)))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)) p0054 p0055
  have p0057 :=
    @g_hncodeprednonemptyminimalndv y v u A (.cv q) dv_cache_0010 dv_cache_0002 dv_cache_0003 dv_cache_0008 dv_cache_0004 dv_cache_0011 dv_cache_0012 dv_cache_0005
  have p0058 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem (.cv q) (syn_cvv))) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (.classMem (.cv v) (.cv q)))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0))) (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u))))) p0056 p0057
  have p0059 :=
    @g_ex (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wne (syn_chncodepredends A (.cv q) v) (syn_c0)) (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u))))) p0058
  have p0060 :=
    @g_pm2_61dne (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q))) (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u))))) (syn_chncodepredends A (.cv q) v) (syn_c0) p0035 p0059
  have p0061 :=
    @g_exlimddv (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (.classMem (.cv v) (.cv q)) (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.classEq (.cv y) (.cv u))))) v dv_cache_0013 dv_cache_0014 p0004 p0060
  exact p0061

noncomputable def g_hncodecmpstrictfrndv
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (syn_wbr (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cfound) (syn_chwcn A))) := by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_q_ne_y : q ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_q : y ≠ q :=
    Ne.symm fresh_q_ne_y
  have fresh_q_ne_u : q ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0005 : q ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ y from (by exact fresh_q_ne_y))
  have dv_cache_0006 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0007 : q ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show y ≠ u from (by exact fresh_y_ne_u))
  have p0000 :=
    @g_hncodecmpsetexg A
  have p0001 :=
    @g_hncodecmpsetexg A
  have p0002 :=
    @g_cnvexg (syn_chncodecmpset A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_ccnv (syn_chncodecmpset A)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_ccnv (syn_chncodecmpset A)) (syn_cvv)) p0000 p0003
  have p0005 :=
    @g_difexg (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chncodecmpset A) (syn_cvv)) (.classMem (syn_ccnv (syn_chncodecmpset A)) (syn_cvv))) (.classMem (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_hwcnexg A
  have p0008 :=
    @g_hncodecmpstrictminndv y u A q dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0009_e02_recanon : Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss (.cv q) (syn_chwcn A)) (syn_wne (.cv q) (syn_c0)))) (syn_wrex u (.cv q) (syn_wral y (.cv q) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)) (.objEq y u))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cvv syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_cdif syn_cin syn_chncodecmpset syn_ccnv syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0008
  have p0009 :=
    @g_frrd (.classMem A (syn_cvv)) q y u (syn_chwcn A) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0005 dv_cache_0004 dv_cache_0014 p0006 p0007 p0009_e02_recanon
  exact p0009

#print axioms g_hncodecmpstrictfrndv

end NFChoice.DirectNominalPrf.WPPReplay
