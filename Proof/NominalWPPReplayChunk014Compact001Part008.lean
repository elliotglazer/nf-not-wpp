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
import NominalWPPReplayChunk014Compact001Part007

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

noncomputable def g_taginjex
    (x : Var) (y : Var) (v : Var) (t : Var) (dv_t_v : t ≠ v) (dv_t_x : t ≠ x) (dv_t_y : t ≠ y) (dv_v_x : v ≠ x) (dv_v_y : v ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({v} : Finset Var) ∪ ({t} : Finset Var)
  have dv_cache_0001 : t ∉ ((Class.cv v)).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_t_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((syn_cxp (.cv v) (syn_csn (syn_c0c)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_t_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex v
  have p0001 :=
    @g_n_0cex
  have p0002 :=
    @g_xpsnen (.cv v) (syn_c0c) p0000 p0001
  have p0003 :=
    @g_ensym (syn_cxp (.cv v) (syn_csn (syn_c0c))) (.cv v)
  have p0004 :=
    @g_mpbi (syn_wbr (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cen) (.cv v)) (syn_wbr (.cv v) (syn_cen) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) p0002 p0003
  have p0005 :=
    @g_bren (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))) t dv_cache_0001 dv_cache_0002
  have p0006 :=
    @g_mpbi (syn_wbr (.cv v) (syn_cen) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) (syn_wex t (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))))) p0004 p0005
  have p0007 :=
    @g_f1of1 (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))) (.cv t)
  have p0008 :=
    @g_ssun1 (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
  have p0009 :=
    @g_a1i (syn_wss (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) p0008
  have p0010 :=
    @g_jca (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) (syn_wf1 (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) (syn_wss (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) p0007 p0009
  have p0011 :=
    @g_f1ss (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (.cv t)
  have p0012 :=
    @g_syl (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) (syn_wa (syn_wf1 (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) (syn_wss (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) p0010 p0011
  have p0013 :=
    @g_eximi (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) t p0012
  have p0014 :=
    Nominal.mp p0006 p0013
  exact p0014

noncomputable def g_qkrelbr
    (A : Class) (B : Class) (C : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_B_C : Disjoint B.fv C.fv) (hyp_qkrelbr_1 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_qkrelbr_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk B C) (syn_cqkrel A)) (.classMem (syn_cop B C) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : x ∉ ((syn_cqkrel A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cqkrel A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Wff.classMem (syn_cop B C) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_C, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classMem (syn_cop (.cv x) (.cv y)) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((Wff.classMem (syn_cop B (.cv y)) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : z ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0019 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qkrel x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_opeq1 (.cv x) B (.cv y)
  have p0002 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_cop (.cv x) (.cv y)) (syn_cop B (.cv y)) A p0001
  have p0003 :=
    @g_opeq2 (.cv y) C B
  have p0004 :=
    @g_eleq1d (.classEq (.cv y) C) (syn_cop B (.cv y)) (syn_cop B C) A p0003
  have p0005 :=
    @g_opkelopkab (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop B (.cv y)) A) (.classMem (syn_cop B C) A) z x y (syn_cqkrel A) B C dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0004 p0000 p0002 p0004 hyp_qkrelbr_1 hyp_qkrelbr_2
  exact p0005

noncomputable def g_fdmemval
    (C : Class) (e : Var) (dv_C_e : e ∉ C.fv) (hyp_fdmemval_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem C (.cv e))) := by
  let proofSupport : Finset Var := C.fv ∪ ({e} : Finset Var)
  have p0000 :=
    (by simpa [syn_cfdmem] using (Nominal.classEqRefl (syn_cfdmem)))
  have p0001 :=
    @g_eleq2i (syn_cfdmem) (syn_ccnvk (syn_csik (syn_cssetk))) (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) p0000
  have p0002 :=
    @g_snex (.cv e)
  have p0003 :=
    @g_snex (syn_csn C)
  have p0004 :=
    @g_opkelcnvk (syn_csn (.cv e)) (syn_csn (syn_csn C)) (syn_csik (syn_cssetk)) p0002 p0003
  have p0005 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_ccnvk (syn_csik (syn_cssetk)))) (.classMem (syn_copk (syn_csn (syn_csn C)) (syn_csn (.cv e))) (syn_csik (syn_cssetk))) p0001 p0004
  have p0006 :=
    @g_snex C
  have p0007 :=
    @g_vex e
  have p0008 :=
    @g_opksnelsik (syn_csn C) (.cv e) (syn_cssetk) p0006 p0007
  have p0009 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem (syn_copk (syn_csn (syn_csn C)) (syn_csn (.cv e))) (syn_csik (syn_cssetk))) (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) p0005 p0008
  have p0010 :=
    @g_vex e
  have p0011 :=
    @g_elssetk C (.cv e) hyp_fdmemval_1 p0010
  have p0012 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) (.classMem C (.cv e)) p0009 p0011
  exact p0012

noncomputable def g_qkrelex
    (A : Class) (hyp_qkrelex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cqkrel A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qkrel x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_setconslem6 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_eqtr4i (syn_cqkrel A) (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (syn_cop (.cv x) (.cv y)) A))))) (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) p0000 p0001
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_vvex
  have p0005 :=
    @g_vvex
  have p0006 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0004 p0005
  have p0007 :=
    @g_xpkex (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_setconslem5
  have p0009 :=
    @g_inex (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0007 p0008
  have p0010 :=
    @g_pw1ex A hyp_qkrelex_1
  have p0011 :=
    @g_pw1ex (syn_cpw1 A) p0010
  have p0012 :=
    @g_imakex (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A)) p0009 p0011
  have p0013 :=
    @g_eqeltri (syn_cqkrel A) (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) (syn_cvv) p0002 p0012
  exact p0013

noncomputable def g_fdmemex
     :
    Nominal.NPrf (.classMem (syn_cfdmem) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cfdmem] using (Nominal.classEqRefl (syn_cfdmem)))
  have p0001 :=
    @g_ssetkex
  have p0002 :=
    @g_sikex (syn_cssetk) p0001
  have p0003 :=
    @g_cnvkex (syn_csik (syn_cssetk)) p0002
  have p0004 :=
    @g_eqeltri (syn_cfdmem) (syn_ccnvk (syn_csik (syn_cssetk))) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_fdprj0ex
     :
    Nominal.NPrf (.classMem (syn_cfdprj0) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cfdprj0] using (Nominal.classEqRefl (syn_cfdprj0)))
  have p0001 :=
    @g_idkex
  have p0002 :=
    @g_ins3kex (syn_cidk) p0001
  have p0003 :=
    @g_eqeltri (syn_cfdprj0) (syn_cins3k (syn_cidk)) (syn_cvv) p0000 p0002
  exact p0003

noncomputable def g_fdprj1ex
     :
    Nominal.NPrf (.classMem (syn_cfdprj1) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cfdprj1] using (Nominal.classEqRefl (syn_cfdprj1)))
  have p0001 :=
    @g_idkex
  have p0002 :=
    @g_ins2kex (syn_cidk) p0001
  have p0003 :=
    @g_eqeltri (syn_cfdprj1) (syn_cins2k (syn_cidk)) (syn_cvv) p0000 p0002
  exact p0003

noncomputable def g_fddomex
    (A : Class) (B : Class) (hyp_fddomex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fddomex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfddom A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cfddom] using (Nominal.classEqRefl (syn_cfddom A B)))
  have p0001 :=
    @g_pw1ex A hyp_fddomex_1
  have p0002 :=
    @g_xpkex B B hyp_fddomex_2 hyp_fddomex_2
  have p0003 :=
    @g_xpkex (syn_cpw1 A) (syn_cxpk B B) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cfddom A B) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_fde0ex
    (A : Class) (B : Class) (hyp_fddomex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fddomex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfde0 A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cfde0] using (Nominal.classEqRefl (syn_cfde0 A B)))
  have p0001 :=
    @g_fdprj0ex
  have p0002 :=
    @g_fdmemex
  have p0003 :=
    @g_cokex (syn_cfdprj0) (syn_cfdmem) p0001 p0002
  have p0004 :=
    @g_fddomex A B hyp_fddomex_1 hyp_fddomex_2
  have p0005 :=
    @g_inex (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B) p0003 p0004
  have p0006 :=
    @g_eqeltri (syn_cfde0 A B) (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_fde1ex
    (A : Class) (B : Class) (hyp_fddomex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fddomex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfde1 A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cfde1] using (Nominal.classEqRefl (syn_cfde1 A B)))
  have p0001 :=
    @g_fdprj1ex
  have p0002 :=
    @g_fdmemex
  have p0003 :=
    @g_cokex (syn_cfdprj1) (syn_cfdmem) p0001 p0002
  have p0004 :=
    @g_fddomex A B hyp_fddomex_1 hyp_fddomex_2
  have p0005 :=
    @g_inex (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B) p0003 p0004
  have p0006 :=
    @g_eqeltri (syn_cfde1 A B) (syn_cin (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B)) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_fdsepex
    (A : Class) (B : Class) (hyp_fddomex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fddomex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdsep A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_cfdsep] using (Nominal.classEqRefl (syn_cfdsep A B)))
  have p0001 :=
    @g_fde0ex A B hyp_fddomex_1 hyp_fddomex_2
  have p0002 :=
    @g_fde1ex A B hyp_fddomex_1 hyp_fddomex_2
  have p0003 :=
    @g_symdifex (syn_cfde0 A B) (syn_cfde1 A B) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cfdsep A B) (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_fdliftex
    (R : Class) (hyp_fdliftex_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdlift R) (syn_cvv)) := by
  let proofSupport : Finset Var := R.fv
  have p0000 :=
    (by simpa [syn_cfdlift] using (Nominal.classEqRefl (syn_cfdlift R)))
  have p0001 :=
    @g_qkrelex R hyp_fdliftex_1
  have p0002 :=
    @g_sikex (syn_cqkrel R) p0001
  have p0003 :=
    @g_eqeltri (syn_cfdlift R) (syn_csik (syn_cqkrel R)) (syn_cvv) p0000 p0002
  exact p0003

noncomputable def g_fdnonminex
    (A : Class) (B : Class) (R : Class) (hyp_fdnonminex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdnonminex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdnonminex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdnonmin R A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cfdnonmin] using (Nominal.classEqRefl (syn_cfdnonmin R A B)))
  have p0001 :=
    @g_fdsepex A B hyp_fdnonminex_2 hyp_fdnonminex_3
  have p0002 :=
    @g_idex
  have p0003 :=
    @g_difex R (syn_cid) hyp_fdnonminex_1 p0002
  have p0004 :=
    @g_fdliftex (syn_cdif R (syn_cid)) p0003
  have p0005 :=
    @g_cnvkex (syn_cfdlift (syn_cdif R (syn_cid))) p0004
  have p0006 :=
    @g_cokex (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))) p0001 p0005
  have p0007 :=
    @g_eqeltri (syn_cfdnonmin R A B) (syn_ccomk (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid))))) (syn_cvv) p0000 p0006
  exact p0007

noncomputable def g_fdminsepex
    (A : Class) (B : Class) (R : Class) (hyp_fdnonminex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdnonminex_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdnonminex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdminsep R A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cfdminsep] using (Nominal.classEqRefl (syn_cfdminsep R A B)))
  have p0001 :=
    @g_fdsepex A B hyp_fdnonminex_2 hyp_fdnonminex_3
  have p0002 :=
    @g_fdnonminex A B R hyp_fdnonminex_1 hyp_fdnonminex_2 hyp_fdnonminex_3
  have p0003 :=
    @g_difex (syn_cfdsep A B) (syn_cfdnonmin R A B) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cfdminsep R A B) (syn_cdif (syn_cfdsep A B) (syn_cfdnonmin R A B)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_fdliftval2
    (x : Var) (R : Class) (e : Var) (c : Var) (d : Var) (dv_R_c : c ∉ R.fv) (dv_R_d : d ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_c_d : c ≠ d) (dv_c_e : c ≠ e) (dv_c_x : c ≠ x) (dv_d_e : d ≠ e) (dv_d_x : d ≠ x) (dv_e_x : e ≠ x) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift R)) (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ R.fv ∪ ({e} : Finset Var) ∪ ({c} : Finset Var) ∪ ({d} : Finset Var)
  have dv_cache_0001 : c ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_c_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : d ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : c ∉ ((syn_csn (.cv e))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_c_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : d ∉ ((syn_csn (.cv e))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : c ∉ ((syn_cqkrel R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : d ∉ ((syn_cqkrel R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : c ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show c ≠ d from (by exact dv_c_d))
  have dv_cache_0008 : Disjoint (R).fv ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (R).fv ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((R).fv) (({c} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show c ∉ (R).fv from (by exact dv_R_c))))))
  have dv_cache_0009 : Disjoint (R).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint (R).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((R).fv) (({d} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show d ∉ (R).fv from (by exact dv_R_d))))))
  have dv_cache_0010 : Disjoint ((Class.cv c)).fv ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show Disjoint ((Class.cv c)).fv ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (c), NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)]; exact (show Disjoint (({c} : Finset Var)) (({d} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show c ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ d from (by exact dv_c_d))))))))
  have p0000 :=
    (by simpa [syn_cfdlift] using (Nominal.classEqRefl (syn_cfdlift R)))
  have p0001 :=
    @g_eleq2i (syn_cfdlift R) (syn_csik (syn_cqkrel R)) (syn_copk (.cv x) (syn_csn (.cv e))) p0000
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_snex (.cv e)
  have p0004 :=
    @g_pm3_2i (.classMem (.cv x) (syn_cvv)) (.classMem (syn_csn (.cv e)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_opkelsikg c d (.cv x) (syn_csn (.cv e)) (syn_cqkrel R) (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_vex c
  have p0008 :=
    @g_vex d
  have p0009 :=
    @g_qkrelbr R (.cv c) (.cv d) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0007 p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv c) R (.cv d))))
  have p0011 :=
    @g_bicomi (syn_wbr (.cv c) R (.cv d)) (.classMem (syn_cop (.cv c) (.cv d)) R) p0010
  have p0012 :=
    @g_bitri (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R)) (.classMem (syn_cop (.cv c) (.cv d)) R) (syn_wbr (.cv c) R (.cv d)) p0009 p0011
  have p0013 :=
    @g_n_3anbi3i (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R)) (syn_wbr (.cv c) R (.cv d)) (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) p0012
  have p0014 :=
    @g_exbii (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d))) d p0013
  have p0015 :=
    @g_exbii (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R)))) (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))) c p0014
  have p0016 :=
    @g_bitri (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_csik (syn_cqkrel R))) (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R))))) (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d))))) p0006 p0015
  have p0017 :=
    @g_bitri (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift R)) (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_csik (syn_cqkrel R))) (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d))))) p0001 p0016
  exact p0017

noncomputable def g_fdliftval1
    (x : Var) (R : Class) (e : Var) (c : Var) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_c_e : c ≠ e) (dv_c_x : c ≠ x) (dv_e_x : e ≠ x) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift R)) (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ R.fv ∪ ({e} : Finset Var) ∪ ({c} : Finset Var)
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_ne_x : d ≠ x := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_ne_e : d ≠ e := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_e_ne_d : e ≠ d :=
    Ne.symm fresh_d_ne_e
  have fresh_d_ne_c : d ≠ c := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_d : c ≠ d :=
    Ne.symm fresh_d_ne_c
  have dv_cache_0001 : c ∉ (R).fv := by
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : d ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : e ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : c ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0006 : c ≠ e := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show c ≠ e from (by exact dv_c_e))
  have dv_cache_0007 : c ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show c ≠ x from (by exact dv_c_x))
  have dv_cache_0008 : d ≠ e := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show d ≠ e from (by exact fresh_d_ne_e))
  have dv_cache_0009 : d ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0010 : e ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show e ≠ x from (by exact dv_e_x))
  have dv_cache_0011 : d ∉ ((Class.cv e)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : d ∉ ((syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_x, fresh_d_ne_c, fresh_d_ne_e, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdliftval2 x R e c d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_vex e
  have p0002 :=
    @g_sneqb (.cv e) (.cv d) p0001
  have p0003 :=
    @g_eqcom (.cv e) (.cv d)
  have p0004 :=
    @g_bitri (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (.classEq (.cv e) (.cv d)) (.classEq (.cv d) (.cv e)) p0002 p0003
  have p0005 :=
    @g_n_3anbi2i (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d)) p0004
  have p0006 :=
    @g_n_3ancoma (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv d) (.cv e)) (syn_wbr (.cv c) R (.cv d))
  have p0007 :=
    @g_bitri (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv d) (.cv e)) (syn_wbr (.cv c) R (.cv d))) (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d))) p0005 p0006
  have p0008 :=
    @g_exbii (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d))) (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d))) d p0007
  have p0009 :=
    @g_exbii (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))) (syn_wex d (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d)))) c p0008
  have p0010 :=
    @g_n_3anass (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d))
  have p0011 :=
    @g_exbii (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d))) (syn_wa (.classEq (.cv d) (.cv e)) (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d)))) d p0010
  have p0012 :=
    @g_vex e
  have p0013 :=
    @g_breq2 (.cv d) (.cv e) (.cv c) R
  have p0014 :=
    @g_anbi2d (.classEq (.cv d) (.cv e)) (syn_wbr (.cv c) R (.cv d)) (syn_wbr (.cv c) R (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) p0013
  have p0015 :=
    @g_ceqsexv (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d))) (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))) d (.cv e) dv_cache_0011 dv_cache_0012 p0012 p0014
  have p0016 :=
    @g_bitri (syn_wex d (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d)))) (syn_wex d (syn_wa (.classEq (.cv d) (.cv e)) (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d))))) (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))) p0011 p0015
  have p0017 :=
    @g_exbii (syn_wex d (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d)))) (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))) c p0016
  have p0018 :=
    @g_bitri (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d))))) (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d))))) (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e)))) p0009 p0017
  have p0019 :=
    @g_bitri (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift R)) (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d))))) (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e)))) p0000 p0018
  exact p0019

noncomputable def g_fdmemvalC
    (B : Class) (C : Class) (e : Var) :
    Nominal.NPrf (.imp (.classMem C B) (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem C (.cv e)))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ ({e} : Finset Var)
  have p0000 :=
    (by simpa [syn_cfdmem] using (Nominal.classEqRefl (syn_cfdmem)))
  have p0001 :=
    @g_eleq2i (syn_cfdmem) (syn_ccnvk (syn_csik (syn_cssetk))) (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) p0000
  have p0002 :=
    @g_snex (.cv e)
  have p0003 :=
    @g_snex (syn_csn C)
  have p0004 :=
    @g_opkelcnvk (syn_csn (.cv e)) (syn_csn (syn_csn C)) (syn_csik (syn_cssetk)) p0002 p0003
  have p0005 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_ccnvk (syn_csik (syn_cssetk)))) (.classMem (syn_copk (syn_csn (syn_csn C)) (syn_csn (.cv e))) (syn_csik (syn_cssetk))) p0001 p0004
  have p0006 :=
    @g_snex C
  have p0007 :=
    @g_vex e
  have p0008 :=
    @g_opksnelsik (syn_csn C) (.cv e) (syn_cssetk) p0006 p0007
  have p0009 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem (syn_copk (syn_csn (syn_csn C)) (syn_csn (.cv e))) (syn_csik (syn_cssetk))) (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) p0005 p0008
  have p0010 :=
    @g_elex C B
  have p0011 :=
    @g_vex e
  have p0012 :=
    @g_a1i (.classMem (.cv e) (syn_cvv)) (.classMem C B) p0011
  have p0013 :=
    @g_jca (.classMem C B) (.classMem C (syn_cvv)) (.classMem (.cv e) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_elssetkg C (.cv e) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (.classMem C B) (syn_wa (.classMem C (syn_cvv)) (.classMem (.cv e) (syn_cvv))) (syn_wb (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) (.classMem C (.cv e))) p0013 p0014
  have p0016 :=
    @g_syl5bb (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) (.classMem C B) (.classMem C (.cv e)) p0009 p0015
  exact p0016

#print axioms g_fdmemvalC

end NFChoice.DirectNominalPrf.WPPReplay
