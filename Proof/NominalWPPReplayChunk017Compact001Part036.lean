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
import NominalWPPReplayChunk017Compact001Part035

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

noncomputable def g_hncodecmpsettransptndv
    (w : Var) (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w))) := by
  let proofSupport : Finset Var := ({w} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_w : x ≠ w := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
  have fresh_y_ne_w : y ≠ w := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
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
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0011 : v ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0012 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0013 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0014 : v ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0015 : w ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0016 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0001 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0002 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)) p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0004 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0003
  have p0005 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0004
  have p0006 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0005
  have p0007 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0008 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0007
  have p0009 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0008
  have p0010 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0009
  have p0011 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0006 p0010
  have p0012 :=
    @g_hncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0011 p0012
  have p0014 :=
    @g_biimpd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0013
  have p0015 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0002 p0014
  have p0016 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0000 p0015
  have p0017 :=
    @g_andi (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0018 :=
    @g_a1i (syn_wb (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (syn_wo (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) p0017
  have p0019 :=
    @g_mpbid (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (syn_wo (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0016 p0018
  have p0020 :=
    @g_simpr (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0021 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)) p0020
  have p0022 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0023 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0022
  have p0024 :=
    @g_simpld (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0023
  have p0025 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0024
  have p0026 :=
    @g_simpl (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0027 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0026
  have p0028 :=
    @g_simprd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0027
  have p0029 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0025 p0028
  have p0030 :=
    @g_hncodecmpsetstrictcutsemclndv y A (.cv v) (.cv w) dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0031 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wb (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))))) p0029 p0030
  have p0032 :=
    @g_biimpd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))) p0031
  have p0033 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))) p0021 p0032
  have p0034 :=
    @g_jca (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wo (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))) p0019 p0033
  have p0035 :=
    @g_hncodecmptransisonisondv w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0036 :=
    @g_hncodecmptransisoncutndv y w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0004 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0037 :=
    @g_jaodan (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))) p0035 p0036
  have p0038 :=
    @g_hncodecmptranscutonisondv x w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0001 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0039 :=
    @g_hncodecmptranscutoncutndv x y w v u A dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0001 dv_cache_0004 dv_cache_0013 dv_cache_0010 dv_cache_0014 dv_cache_0011 dv_cache_0015 dv_cache_0012 dv_cache_0016
  have p0040 :=
    @g_jaodan (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))) p0038 p0039
  have p0041 :=
    @g_jaoian (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0037 p0040
  have p0042 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (syn_wo (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (syn_wo (syn_wbr (.cv v) (syn_chwniso A) (.cv w)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv w)) (syn_wbr (.cv v) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv w)) (.cv y)))))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0034 p0041
  exact p0042

noncomputable def g_hncodecmpsettransndv
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))) := by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
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
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have fresh_u_ne_w : u ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_u : w ≠ u :=
    Ne.symm fresh_u_ne_w
  have fresh_v_ne_w : v ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_v : w ≠ v :=
    Ne.symm fresh_v_ne_w
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
  have dv_cache_0003 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((syn_chncodecmpset A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : v ∉ ((syn_chncodecmpset A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_chncodecmpset A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : u ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0014 : u ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0015 : v ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have p0000 :=
    @g_hncodecmpsetexg A
  have p0001 :=
    @g_hwcnexg A
  have p0002 :=
    @g_simp1 (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0003 :=
    @g_simp2 (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0004 :=
    @g_simp1d (syn_w3a (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0003
  have p0005 :=
    @g_simp2 (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0006 :=
    @g_simp2d (syn_w3a (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0005
  have p0007 :=
    @g_jca (syn_w3a (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0004 p0006
  have p0008 :=
    @g_simp2 (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0009 :=
    @g_simp3d (syn_w3a (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0008
  have p0010 :=
    @g_jca (syn_w3a (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)) p0007 p0009
  have p0011 :=
    @g_jca (syn_w3a (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A))) p0002 p0010
  have p0012 :=
    @g_simp3 (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))
  have p0013 :=
    @g_jca (syn_w3a (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w))) p0011 p0012
  have p0014 :=
    @g_hncodecmpsettransptndv w v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0015 :=
    @g_syl (syn_w3a (.classMem A (syn_cvv)) (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv w) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv w)))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv w)) p0013 p0014
  have p0016 :=
    @g_trrd (.classMem A (syn_cvv)) u v w (syn_chwcn A) (syn_chncodecmpset A) (syn_cvv) (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0000 p0001 p0015
  exact p0016

#print axioms g_hncodecmpsettransndv

end NFChoice.DirectNominalPrf.WPPReplay
