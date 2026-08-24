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
import NominalWPPReplayChunk017Compact001Part037

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

noncomputable def g_hncodecmpstrictnoreversendv
    (x : Var) (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.imp (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_v : y ≠ v := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : v ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_u, fresh_z_ne_x, fresh_z_ne_v, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0006 : u ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0007 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : y ∉ ((syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, fresh_y_ne_z, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, fresh_y_ne_x, fresh_y_ne_v, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Wff.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_v_x), (Ne.symm dv_u_x), dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, (Ne.symm dv_u_x), (Ne.symm dv_v_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0001 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0000
  have p0002 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0001
  have p0003 :=
    @g_simp2 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0004 :=
    @g_jca (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0002 p0003
  have p0005 :=
    @g_hnwcutcodeselfnoisondv x v A dv_cache_0001
  have p0006 :=
    @g_syl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.neg (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0004 p0005
  have p0007 :=
    @g_simpl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
  have p0008 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0009 :=
    @g_simpld (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0008
  have p0010 :=
    @g_hwnisoer A
  have p0011 :=
    @g_syl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A)) p0009 p0010
  have p0012 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A)) p0007 p0011
  have p0013 :=
    @g_simpl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
  have p0014 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0015 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0014
  have p0016 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0015
  have p0017 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv v) (syn_chwcn A)) p0013 p0016
  have p0018 :=
    @g_simpl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
  have p0019 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0020 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0019
  have p0021 :=
    @g_simpld (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0020
  have p0022 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) p0018 p0021
  have p0023 :=
    @g_simpl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
  have p0024 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0025 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0024
  have p0026 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0025
  have p0027 :=
    @g_simp2 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0028 :=
    @g_jca (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0026 p0027
  have p0029 :=
    @g_hnwcutcodeambientndv x v A dv_cache_0001
  have p0030 :=
    @g_syl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwcn A)) p0028 p0029
  have p0031 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwcn A)) p0023 p0030
  have p0032 :=
    @g_simpr (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
  have p0033 :=
    @g_simpl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
  have p0034 :=
    @g_simp3 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0035 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0033 p0034
  have p0036 :=
    @g_ertrd (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (syn_chwcn A) (syn_chwniso A) (.cv v) (.cv u) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) p0012 p0017 p0022 p0031 p0032 p0035
  have p0037 :=
    @g_expcom (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0036
  have p0038 :=
    @g_com12 (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0037
  have p0039 :=
    @g_mtod (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0006 p0038
  have p0040 :=
    @g_simpl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
  have p0041 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0042 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0041
  have p0043 :=
    @g_simpld (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0042
  have p0044 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) p0040 p0043
  have p0045 :=
    @g_simpr (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
  have p0046 :=
    @g_jca (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))) p0044 p0045
  have p0047 :=
    @g_hnwcutcodeselfnoisondv z u A dv_cache_0002
  have p0048 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (.neg (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))) p0046 p0047
  have p0049 :=
    @g_nrexdv (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))) z (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0003 p0048
  have p0050 :=
    @g_simp1 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0051 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0052 :=
    @g_simpld (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0051
  have p0053 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) p0050 p0052
  have p0054 :=
    @g_simp1 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0055 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0056 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0055
  have p0057 :=
    @g_simpld (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0056
  have p0058 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) p0054 p0057
  have p0059 :=
    @g_simp1 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0060 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0061 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0060
  have p0062 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0061
  have p0063 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv v) (syn_chwcn A)) p0059 p0062
  have p0064 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0058 p0063
  have p0065 :=
    @g_simp1 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0066 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0067 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0066
  have p0068 :=
    @g_simpld (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0067
  have p0069 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) p0065 p0068
  have p0070 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0064 p0069
  have p0071 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A))) p0053 p0070
  have p0072 :=
    @g_simp1 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0073 :=
    @g_simp2 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0074 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0072 p0073
  have p0075 :=
    @g_simp1 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0076 :=
    @g_simp3 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0077 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0075 p0076
  have p0078 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) p0074 p0077
  have p0079 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0071 p0078
  have p0080 :=
    @g_simp1 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0081 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0082 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0081
  have p0083 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0082
  have p0084 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv v) (syn_chwcn A)) p0080 p0083
  have p0085 :=
    @g_simp1 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0086 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0087 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0086
  have p0088 :=
    @g_simpld (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0087
  have p0089 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) p0085 p0088
  have p0090 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0084 p0089
  have p0091 :=
    @g_simp2 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0092 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) p0090 p0091
  have p0093 :=
    @g_simp3 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0094 :=
    @g_simp1 (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0095 :=
    @g_simp2 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0096 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0094 p0095
  have p0097 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0093 p0096
  have p0098 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) p0092 p0097
  have p0099 :=
    @g_hnwcutcodetransportintocutndv x y z u v A dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0100 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))) p0098 p0099
  have p0101 :=
    @g_jca (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))) p0079 p0100
  have p0102 :=
    @g_hnwcutcodestrictextendndv x z u v u A dv_cache_0002 dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0006 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0103 :=
    @g_syl (syn_w3a (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))) p0101 p0102
  have p0104 :=
    @g_n_3exp (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))) p0103
  have p0105 :=
    @g_rexlimdv (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))) y (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0008 dv_cache_0009 p0104
  have p0106 :=
    @g_mtod (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))) p0049 p0105
  have p0107 :=
    @g_jca (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.neg (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (.neg (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))) p0039 p0106
  have p0108 :=
    @g_ioran (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
  have p0109 :=
    @g_a1i (syn_wb (.neg (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))))) (syn_wa (.neg (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (.neg (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))))) (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0108
  have p0110 :=
    @g_mpbird (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.neg (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))))) (syn_wa (.neg (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) (.neg (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))))) p0107 p0109
  have p0111 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0112 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0111
  have p0113 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0112
  have p0114 :=
    @g_simp1 (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0115 :=
    @g_simprd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0114
  have p0116 :=
    @g_simpld (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0115
  have p0117 :=
    @g_jca (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0113 p0116
  have p0118 :=
    @g_hncodecmpsetstrictcutsemclndv y A (.cv v) (.cv u) dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0119 :=
    @g_syl (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (syn_wb (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))))) p0117 p0118
  have p0120 :=
    @g_biimpd (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))) p0119
  have p0121 :=
    @g_mtod (syn_w3a (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))) p0110 p0120
  have p0122 :=
    @g_n_3exp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) p0121
  have p0123 :=
    @g_rexlimdv (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) (.neg (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u))) x (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0013 dv_cache_0014 p0122
  exact p0123

#print axioms g_hncodecmpstrictnoreversendv

end NFChoice.DirectNominalPrf.WPPReplay
