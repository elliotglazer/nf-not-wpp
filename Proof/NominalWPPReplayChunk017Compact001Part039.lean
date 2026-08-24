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
import NominalWPPReplayChunk017Compact001Part038

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

noncomputable def g_hncodecmpkerptndv
    (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_v : y ≠ v := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : v ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0006 : x ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0009 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0001 :=
    @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0002 :=
    @g_sylib (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0000 p0001
  have p0003 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0002
  have p0004 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0005 :=
    @g_hncodecmpstrictnoreversendv x v u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0006 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.imp (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))) p0004 p0005
  have p0007 :=
    @g_mt2d (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0003 p0006
  have p0008 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0009 :=
    @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0010 :=
    @g_sylib (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0008 p0009
  have p0011 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0010
  have p0012 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0013 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0014 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0012 p0013
  have p0015 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0003 dv_cache_0006 dv_cache_0007
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0014 p0015
  have p0017 :=
    @g_mpbid (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0011 p0016
  have p0018 :=
    @g_orcomd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0017
  have p0019 :=
    @g_orcanai (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0018
  have p0020 :=
    @g_mpdan (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (.neg (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0007 p0019
  have p0021 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0022 :=
    @g_orc (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0021 p0022
  have p0024 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0025 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0024 p0025
  have p0027 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0003 dv_cache_0006 dv_cache_0007
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0026 p0027
  have p0029 :=
    @g_mpbird (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0023 p0028
  have p0030 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0031 :=
    @g_hwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0008
  have p0032 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) p0030 p0031
  have p0033 :=
    @g_orc (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))) p0032 p0033
  have p0035 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0036 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0037 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0035 p0036
  have p0038 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0037
  have p0039 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0040 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0039 p0040
  have p0042 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0041
  have p0043 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0038 p0042
  have p0044 :=
    @g_hncodecmpsetstrictcutsemclndv y A (.cv v) (.cv u) dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0045 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wb (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))))) p0043 p0044
  have p0046 :=
    @g_mpbird (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))) p0034 p0045
  have p0047 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0029 p0046
  have p0048 :=
    @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0049 :=
    @g_sylibr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0047 p0048
  have p0050 :=
    @g_impbida (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0020 p0049
  exact p0050

noncomputable def g_hncodecmplnkerndv
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A))) := by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_u_ne_x : u ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_v_ne_x : v ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : v ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0006 : x ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0009 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((syn_clnker (syn_chncodecmpset A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : v ∉ ((syn_clnker (syn_chncodecmpset A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : u ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : v ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : u ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : v ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0001 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0002 :=
    @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0003 :=
    @g_sylib (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0001 p0002
  have p0004 :=
    @g_simpld (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0003
  have p0005 :=
    @g_hncodecmpsetssxpndv A
  have p0006 :=
    @g_brel (.cv u) (.cv v) (syn_chwcn A) (syn_chwcn A) (syn_chncodecmpset A) p0005
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0004 p0006
  have p0008 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0000 p0007
  have p0009 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0010 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0008 p0009
  have p0011 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0012 :=
    @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0013 :=
    @g_sylib (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0011 p0012
  have p0014 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0013
  have p0015 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0016 :=
    @g_hncodecmpstrictnoreversendv x v u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.imp (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))) p0015 p0016
  have p0018 :=
    @g_mt2d (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0014 p0017
  have p0019 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0020 :=
    @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0021 :=
    @g_sylib (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0019 p0020
  have p0022 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0021
  have p0023 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))
  have p0024 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0023 p0024
  have p0026 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0003 dv_cache_0006 dv_cache_0007
  have p0027 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0025 p0026
  have p0028 :=
    @g_mpbid (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0022 p0027
  have p0029 :=
    @g_orcomd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0028
  have p0030 :=
    @g_orcanai (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0029
  have p0031 :=
    @g_mpdan (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (.neg (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0018 p0030
  have p0032 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0010 p0031
  have p0033 :=
    @g_ex (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0032
  have p0034 :=
    @g_simpl (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0035 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0036 :=
    @g_breldm (.cv u) (.cv v) (syn_chwniso A)
  have p0037 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem (.cv u) (syn_cdm (syn_chwniso A))) p0035 p0036
  have p0038 :=
    @g_hwnisodm A
  have p0039 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A)) (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) p0038
  have p0040 :=
    @g_eleqtrd (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.cv u) (syn_cdm (syn_chwniso A)) (syn_chwcn A) p0037 p0039
  have p0041 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0042 :=
    @g_hwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0008
  have p0043 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) p0041 p0042
  have p0044 :=
    @g_breldm (.cv v) (.cv u) (syn_chwniso A)
  have p0045 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (.classMem (.cv v) (syn_cdm (syn_chwniso A))) p0043 p0044
  have p0046 :=
    @g_hwnisodm A
  have p0047 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A)) (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) p0046
  have p0048 :=
    @g_eleqtrd (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.cv v) (syn_cdm (syn_chwniso A)) (syn_chwcn A) p0045 p0047
  have p0049 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0040 p0048
  have p0050 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0034 p0049
  have p0051 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0052 :=
    @g_jca (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0050 p0051
  have p0053 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0054 :=
    @g_orc (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0055 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0053 p0054
  have p0056 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0057 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0058 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0056 p0057
  have p0059 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0003 dv_cache_0006 dv_cache_0007
  have p0060 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0058 p0059
  have p0061 :=
    @g_mpbird (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0055 p0060
  have p0062 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0063 :=
    @g_hwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0008
  have p0064 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) p0062 p0063
  have p0065 :=
    @g_orc (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
  have p0066 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))) p0064 p0065
  have p0067 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0068 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0069 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0067 p0068
  have p0070 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0069
  have p0071 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
  have p0072 :=
    @g_simpr (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0073 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0071 p0072
  have p0074 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0073
  have p0075 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0070 p0074
  have p0076 :=
    @g_hncodecmpsetstrictcutsemclndv y A (.cv v) (.cv u) dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0077 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wb (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))))) p0075 p0076
  have p0078 :=
    @g_mpbird (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))) p0066 p0077
  have p0079 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0061 p0078
  have p0080 :=
    @g_brlnker (syn_chncodecmpset A) (.cv u) (.cv v)
  have p0081 :=
    @g_sylibr (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0079 p0080
  have p0082 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0052 p0081
  have p0083 :=
    @g_ex (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) p0082
  have p0084 :=
    @g_impbid (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0033 p0083
  have p0085 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v))))
  have p0086 :=
    @g_bicomi (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_clnker (syn_chncodecmpset A))) p0085
  have p0087 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))))
  have p0088 :=
    @g_bicomi (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwniso A)) p0087
  have p0089 :=
    @g_n_3bitr4g (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_clnker (syn_chncodecmpset A)) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_clnker (syn_chncodecmpset A))) (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwniso A)) p0084 p0086 p0088
  have p0090 :=
    @g_eqrelrdv (.classMem A (syn_cvv)) u v (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0008 p0089
  exact p0090

#print axioms g_hncodecmplnkerndv

end NFChoice.DirectNominalPrf.WPPReplay
