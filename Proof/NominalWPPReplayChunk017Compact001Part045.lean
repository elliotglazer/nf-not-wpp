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
import NominalWPPReplayChunk017Compact001Part044

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

noncomputable def g_hncodepredemptyminimalndv
    (y : Var) (v : Var) (A : Class) (X : Class) (dv_A_v : v ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_X_y : y ∉ X.fv) (dv_v_y : v ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (syn_wral y X (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv v))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({v} : Finset Var) ∪ A.fv ∪ X.fv
  let t : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have fresh_t_ne_v : t ≠ v := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_t : v ≠ t :=
    Ne.symm fresh_t_ne_v
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_v : a ≠ v := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_a : v ≠ a :=
    Ne.symm fresh_a_ne_v
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_t_ne_a : t ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_t : a ≠ t :=
    Ne.symm fresh_t_ne_a
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ v from (by exact Ne.symm dv_v_y))
  have dv_cache_0005 : y ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ t from (by exact fresh_y_ne_t))
  have dv_cache_0006 : v ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ t from (by exact fresh_v_ne_t))
  have dv_cache_0007 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_t, fresh_a_ne_v, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ v from (by exact fresh_a_ne_v))
  have dv_cache_0012 : a ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ t from (by exact fresh_a_ne_t))
  have dv_cache_0013 : t ∉ ((Wff.classEq (.cv y) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, fresh_t_not_X, fresh_t_ne_v, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_X_y, (Ne.symm dv_v_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
  have p0001 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
  have p0002 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)
  have p0003 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))
  have p0004 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0003
  have p0005 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (.classMem A (syn_cvv)) p0001 p0005
  have p0007 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
  have p0008 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)
  have p0009 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))
  have p0010 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0009
  have p0011 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0010
  have p0012 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) p0008 p0011
  have p0013 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)
  have p0014 :=
    @g_sseldd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) X (syn_chwcn A) (.cv y) p0012 p0013
  have p0015 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (.classMem (.cv y) (syn_chwcn A)) p0007 p0014
  have p0016 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
  have p0017 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)
  have p0018 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))
  have p0019 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0018
  have p0020 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0019
  have p0021 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))
  have p0022 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0021
  have p0023 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0022
  have p0024 :=
    @g_sseldd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) X (syn_chwcn A) (.cv v) p0020 p0023
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv v) (syn_chwcn A)) p0017 p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (.classMem (.cv v) (syn_chwcn A)) p0016 p0025
  have p0027 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0015 p0026
  have p0028 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0006 p0027
  have p0029 :=
    @g_hncodecmpstrictbrndv t v y A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0030 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (syn_wrex t (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) p0028 p0029
  have p0031 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (syn_wrex t (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))) p0000 p0030
  have p0032 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
  have p0033 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
  have p0034 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)
  have p0035 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classEq (syn_chncodepredends A X v) (syn_c0)) p0034 p0035
  have p0037 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (.classEq (syn_chncodepredends A X v) (syn_c0)) p0033 p0036
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (.classEq (syn_chncodepredends A X v) (syn_c0)) p0032 p0037
  have p0039 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
  have p0040 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))) p0039
  have p0041 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
  have p0042 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
  have p0043 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (.classMem (.cv y) X) p0042 p0043
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (.classMem (.cv y) X) p0041 p0044
  have p0046 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
  have p0047 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))) p0046
  have p0048 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (.classMem (.cv y) X) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))) p0045 p0047
  have p0049 :=
    @g_breq1 (.cv a) (.cv y) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)) (syn_chwniso A)
  have p0050 :=
    @g_rspcev (syn_wbr (.cv a) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))) a (.cv y) X dv_cache_0007 dv_cache_0008 dv_cache_0009 p0049
  have p0051 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (syn_wa (.classMem (.cv y) X) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))) (syn_wrex a X (syn_wbr (.cv a) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))) p0048 p0050
  have p0052 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex a X (syn_wbr (.cv a) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))) p0040 p0051
  have p0053 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
  have p0054 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
  have p0055 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)
  have p0056 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))
  have p0057 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0056
  have p0058 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0057
  have p0059 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))
  have p0060 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0059
  have p0061 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0060
  have p0062 :=
    @g_sseldd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) X (syn_chwcn A) (.cv v) p0058 p0061
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv v) (syn_chwcn A)) p0055 p0062
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (.classMem (.cv v) (syn_chwcn A)) p0054 p0063
  have p0065 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (.classMem (.cv v) (syn_chwcn A)) p0053 p0064
  have p0066 :=
    @g_hncodepredendsmemndv t v a A X dv_cache_0010 dv_cache_0002 dv_cache_0008 dv_cache_0011 dv_cache_0012
  have p0067 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (.classMem (.cv v) (syn_chwcn A)) (syn_wb (.classMem (.cv t) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex a X (syn_wbr (.cv a) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))))) p0065 p0066
  have p0068 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (.classMem (.cv t) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex a X (syn_wbr (.cv a) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) p0052 p0067
  have p0069 :=
    @g_ne0i (syn_chncodepredends A X v) (.cv t)
  have p0070 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (.classMem (.cv t) (syn_chncodepredends A X v)) (syn_wne (syn_chncodepredends A X v) (syn_c0)) p0068 p0069
  have p0071 :=
    @g_pm2_21ddne (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))) (.classEq (.cv y) (.cv v)) (syn_chncodepredends A X v) (syn_c0) p0038 p0070
  have p0072 :=
    @g_rexlimddv (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))) (.classEq (.cv y) (.cv v)) t (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0013 dv_cache_0014 p0031 p0071
  have p0073 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv v)) p0072
  have p0074 :=
    @g_ralrimiva (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))) (.classEq (syn_chncodepredends A X v) (syn_c0))) (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)) (.classEq (.cv y) (.cv v))) y X dv_cache_0015 p0073
  exact p0074

noncomputable def g_wefrndv
    (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cfound) D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0001 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0001 p0002
  have p0004 :=
    @g_simprbi (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0003
  exact p0004

#print axioms g_wefrndv

end NFChoice.DirectNominalPrf.WPPReplay
