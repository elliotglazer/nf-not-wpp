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
import NominalWPPReplayChunk017Compact001Part015

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

noncomputable def g_wppqkrelrestypedenqkndv
    (A : Class) (B : Class) (hyp_wppqkrelresf1oqkndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_wppqkrelresf1oqkndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) (syn_cqkrel (syn_cxp A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_wppqkrelresfnndv A B hyp_wppqkrelresf1oqkndv_1 hyp_wppqkrelresf1oqkndv_2
  have p0001 :=
    @g_wppqkrelrescnvfunndv A B hyp_wppqkrelresf1oqkndv_1 hyp_wppqkrelresf1oqkndv_2
  have p0002 :=
    @g_wppqkrelresrangevalndv (syn_cxp A B)
  have p0003 :=
    @g_n_3pm3_2i (syn_wfn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wfun (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))) (.classEq (syn_crn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (syn_cqkrel (syn_cxp A B))) p0000 p0001 p0002
  have p0004 :=
    @g_dff1o2 (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cqkrel (syn_cxp A B)) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0005 :=
    @g_mpbir (syn_wf1o (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cqkrel (syn_cxp A B))) (syn_w3a (syn_wfn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wfun (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))) (.classEq (syn_crn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (syn_cqkrel (syn_cxp A B)))) p0003 p0004
  have p0006 :=
    @g_wppqkrelkernelexndv
  have p0007 :=
    @g_kqrelex (syn_cwppqkrelkernel) p0006
  have p0008 :=
    @g_xpex A B hyp_wppqkrelresf1oqkndv_1 hyp_wppqkrelresf1oqkndv_2
  have p0009 :=
    @g_pw1ex (syn_cxp A B) p0008
  have p0010 :=
    @g_pw1ex (syn_cpw1 (syn_cxp A B)) p0009
  have p0011 :=
    @g_resex (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))) p0007 p0010
  have p0012 :=
    @g_f1oen (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cqkrel (syn_cxp A B)) (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) p0011
  have p0013 :=
    Nominal.mp p0005 p0012
  exact p0013

noncomputable def g_wppqkrelxprebasendv
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cqkrel (syn_cxp A B)) (syn_cxpk A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
  have dv_cache_0001 : x ∉ ((syn_cxp A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((syn_cqkrel (syn_cxp A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_cxpk A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qkrel x y z (syn_cxp A B) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_eleq2i (syn_cqkrel (syn_cxp A B)) (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)))))) (.cv z) p0000
  have p0002 :=
    @g_abid (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B))))) z
  have p0003 :=
    @g_bitri (.classMem (.cv z) (syn_cqkrel (syn_cxp A B))) (.classMem (.cv z) (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B))))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B))))) p0001 p0002
  have p0004 :=
    @g_opelxp (.cv x) (.cv y) A B
  have p0005 :=
    @g_anbi2i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) p0004
  have p0006 :=
    @g_n_2exbii (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B))) (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) x y p0005
  have p0007 :=
    @g_bitri (.classMem (.cv z) (syn_cqkrel (syn_cxp A B))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))))) p0003 p0006
  have p0008 :=
    @g_elxpk x y (.cv z) A B dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0004
  have p0009 :=
    @g_bicomi (.classMem (.cv z) (syn_cxpk A B)) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))))) p0008
  have p0010 :=
    @g_bitri (.classMem (.cv z) (syn_cqkrel (syn_cxp A B))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))))) (.classMem (.cv z) (syn_cxpk A B)) p0007 p0009
  have p0011 :=
    @g_eqriv z (syn_cqkrel (syn_cxp A B)) (syn_cxpk A B) dv_cache_0013 dv_cache_0014 p0010
  exact p0011

noncomputable def g_wppqkrelrestypedenndv
    (A : Class) (B : Class) (hyp_wppqkrelresf1ondv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_wppqkrelresf1ondv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) (syn_cxpk A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_wppqkrelrestypedenqkndv A B hyp_wppqkrelresf1ondv_1 hyp_wppqkrelresf1ondv_2
  have p0001 :=
    @g_wppqkrelxprebasendv A B
  have p0002 :=
    @g_breq2i (syn_cqkrel (syn_cxp A B)) (syn_cxpk A B) (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) p0001
  have p0003 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) (syn_cqkrel (syn_cxp A B))) (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) (syn_cxpk A B)) p0000 p0002
  exact p0003

noncomputable def g_hncardmonodndv
    (A : Class) (D : Class) (hyp_hncardmonodndv_1 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hncardmonodndv_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wss D A) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  have p0000 :=
    @g_hncardeqdndv D (syn_cif (syn_wss D A) D (syn_c0))
  have p0001 :=
    @g_breq1d (.classEq D (syn_cif (syn_wss D A) D (syn_c0))) (syn_chncard D) (syn_chncard (syn_cif (syn_wss D A) D (syn_c0))) (syn_chncard A) (syn_clec) p0000
  have p0002 :=
    @g_iftrue (syn_wss D A) D (syn_c0)
  have p0003 :=
    @g_id (syn_wss D A)
  have p0004 :=
    @g_eqsstrd (syn_wss D A) (syn_cif (syn_wss D A) D (syn_c0)) D A p0002 p0003
  have p0005 :=
    @g_iffalse (syn_wss D A) D (syn_c0)
  have p0006 :=
    @g_n_0ss A
  have p0007 :=
    @g_a1i (syn_wss (syn_c0) A) (.neg (syn_wss D A)) p0006
  have p0008 :=
    @g_eqsstrd (.neg (syn_wss D A)) (syn_cif (syn_wss D A) D (syn_c0)) (syn_c0) A p0005 p0007
  have p0009 :=
    @g_pm2_61i (syn_wss D A) (syn_wss (syn_cif (syn_wss D A) D (syn_c0)) A) p0004 p0008
  have p0010 :=
    @g_n_0ex
  have p0011 :=
    @g_pm3_2i (.classMem D (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) hyp_hncardmonodndv_1 p0010
  have p0012 :=
    @g_ifcl (syn_wss D A) D (syn_c0) (syn_cvv)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_hncardmono A (syn_cif (syn_wss D A) D (syn_c0)) p0009 p0013 hyp_hncardmonodndv_2
  have p0015 :=
    @g_dedth (syn_wss D A) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A)) (syn_wbr (syn_chncard (syn_cif (syn_wss D A) D (syn_c0))) (syn_clec) (syn_chncard A)) D (syn_c0) p0001 p0014
  exact p0015

noncomputable def g_hncardf1leimpndv
    (A : Class) (D : Class) (F : Class) (hyp_hncardf1leimpndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hncardf1leimpndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hncardf1leimpndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wf1 F D A) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ F.fv
  have p0000 :=
    @g_f1f1orn D A F
  have p0001 :=
    @g_hncardf1oimpndv D (syn_crn F) F hyp_hncardf1leimpndv_1
  have p0002 :=
    @g_syl (syn_wf1 F D A) (syn_wf1o F D (syn_crn F)) (.classEq (syn_chncard D) (syn_chncard (syn_crn F))) p0000 p0001
  have p0003 :=
    @g_f1f D A F
  have p0004 :=
    @g_frn D A F
  have p0005 :=
    @g_syl (syn_wf1 F D A) (syn_wf F D A) (syn_wss (syn_crn F) A) p0003 p0004
  have p0006 :=
    @g_rnex F hyp_hncardf1leimpndv_1
  have p0007 :=
    @g_hncardmonodndv A (syn_crn F) p0006 hyp_hncardf1leimpndv_3
  have p0008 :=
    @g_syl (syn_wf1 F D A) (syn_wss (syn_crn F) A) (syn_wbr (syn_chncard (syn_crn F)) (syn_clec) (syn_chncard A)) p0005 p0007
  have p0009 :=
    @g_eqbrtrd (syn_wf1 F D A) (syn_chncard D) (syn_chncard (syn_crn F)) (syn_chncard A) (syn_clec) p0002 p0008
  exact p0009

noncomputable def g_hncardnclecndv
    (A : Class) (D : Class) (hyp_hncardnclecndv_1 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hncardnclecndv_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A)) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nclenc D A f dv_cache_0001 dv_cache_0002 hyp_hncardnclecndv_1 hyp_hncardnclecndv_2
  have p0001 :=
    @g_biimpi (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A)) (syn_wex f (syn_wf1 (.cv f) D A)) p0000
  have p0002 :=
    @g_vex f
  have p0003 :=
    @g_hncardf1leimpndv A D (.cv f) p0002 hyp_hncardnclecndv_1 hyp_hncardnclecndv_2
  have p0004 :=
    @g_exlimiv (syn_wf1 (.cv f) D A) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A)) f dv_cache_0003 p0003
  have p0005 :=
    @g_syl (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A)) (syn_wex f (syn_wf1 (.cv f) D A)) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A)) p0001 p0004
  exact p0005

noncomputable def g_hnordcardnclecndv
    (A : Class) (D : Class) (hyp_hnordcardnclecndv_1 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnordcardnclecndv_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A)) (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A)))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  have p0000 :=
    @g_hncardnclecndv A D hyp_hnordcardnclecndv_1 hyp_hnordcardnclecndv_2
  have p0001 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard D)))
  have p0002 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard A)))
  have p0003 :=
    @g_breq12i (syn_chncard D) (syn_cnc (syn_chnord D)) (syn_chncard A) (syn_cnc (syn_chnord A)) (syn_clec) p0001 p0002
  have p0004 :=
    @g_biimpi (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A)) (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A))) p0003
  have p0005 :=
    @g_syl (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A)) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A)) (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A))) p0000 p0004
  exact p0005

noncomputable def g_wppqkrelliteralenndv
    (X : Class) (hyp_wppqkrelliteralenndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cxp (syn_cxpk X X) (syn_cnnc)) (syn_cen) (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc))) := by
  let proofSupport : Finset Var := X.fv
  have p0000 :=
    @g_wppqkrelrestypedenndv X X hyp_wppqkrelliteralenndv_1 hyp_wppqkrelliteralenndv_1
  have p0001 :=
    @g_ensym (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cxpk X X)
  have p0002 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cen) (syn_cxpk X X)) (syn_wbr (syn_cxpk X X) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) p0000 p0001
  have p0003 :=
    @g_nncex
  have p0004 :=
    @g_enrflx (syn_cnnc) p0003
  have p0005 :=
    @g_pm3_2i (syn_wbr (syn_cxpk X X) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) (syn_wbr (syn_cnnc) (syn_cen) (syn_cnnc)) p0002 p0004
  have p0006 :=
    @g_xpen (syn_cxpk X X) (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc) (syn_cnnc)
  have p0007 :=
    Nominal.mp p0005 p0006
  exact p0007

noncomputable def g_wppqkrelliteralnceqndv
    (X : Class) (hyp_wppqkrelliteralnceqndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc)))) := by
  let proofSupport : Finset Var := X.fv
  have p0000 :=
    @g_wppqkrelliteralenndv X hyp_wppqkrelliteralnceqndv_1
  have p0001 :=
    @g_xpkex X X hyp_wppqkrelliteralnceqndv_1 hyp_wppqkrelliteralnceqndv_1
  have p0002 :=
    @g_nncex
  have p0003 :=
    @g_xpex (syn_cxpk X X) (syn_cnnc) p0001 p0002
  have p0004 :=
    @g_eqnc (syn_cxp (syn_cxpk X X) (syn_cnnc)) (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc)) p0003
  have p0005 :=
    @g_mpbir (.classEq (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc)))) (syn_wbr (syn_cxp (syn_cxpk X X) (syn_cnnc)) (syn_cen) (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc))) p0000 p0004
  exact p0005

noncomputable def g_hnordlnquoeq
    (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_hnordlnquoeq_1 : Nominal.NPrf (.classEq (syn_clnker R) (syn_chwniso A))) :
    Nominal.NPrf (.classEq (syn_clnquo R (syn_chwcn A)) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_clnquo] using (Nominal.classEqRefl (syn_clnquo R (syn_chwcn A))))
  have p0001 :=
    @g_qseq2 (syn_clnker R) (syn_chwniso A) (syn_chwcn A)
  have p0002 :=
    Nominal.mp hyp_hnordlnquoeq_1 p0001
  have p0003 :=
    @g_eqtri (syn_clnquo R (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker R)) (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0000 p0002
  have p0004 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0005 :=
    @g_eqcomi (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0004
  have p0006 :=
    @g_eqtri (syn_clnquo R (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A) p0003 p0005
  exact p0006

noncomputable def g_hnordwefromcmp
    (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_hnordwefromcmp_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_hnordwefromcmp_2 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_hnordwefromcmp_3 : Nominal.NPrf (.classMem (syn_cop R (syn_chwcn A)) (syn_clnpwc (syn_chwcn A)))) (hyp_hnordwefromcmp_4 : Nominal.NPrf (.classEq (syn_clnker R) (syn_chwniso A))) :
    Nominal.NPrf (syn_wbr (syn_clnqord R (syn_chwcn A)) (syn_cwe) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have dv_cache_0001 : Disjoint ((syn_chwcn A)).fv (R).fv := by
    exact (show Disjoint ((syn_chwcn A)).fv (R).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn]; exact (show Disjoint (A).fv (R).fv from (by exact dv_A_R))))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @g_hwcnexg A
  have p0001 :=
    Nominal.mp hyp_hnordwefromcmp_1 p0000
  have p0002 :=
    @g_lnworigqordwe (syn_chwcn A) R dv_cache_0001 p0001 hyp_hnordwefromcmp_2 hyp_hnordwefromcmp_3
  have p0003 :=
    @g_hnordlnquoeq A R dv_cache_0002 hyp_hnordwefromcmp_4
  have p0004 :=
    @g_breq2i (syn_clnquo R (syn_chwcn A)) (syn_chnord A) (syn_clnqord R (syn_chwcn A)) (syn_cwe) p0003
  have p0005 :=
    @g_mpbi (syn_wbr (syn_clnqord R (syn_chwcn A)) (syn_cwe) (syn_clnquo R (syn_chwcn A))) (syn_wbr (syn_clnqord R (syn_chwcn A)) (syn_cwe) (syn_chnord A)) p0002 p0004
  exact p0005

noncomputable def g_hncodecutfnfn
     :
    Nominal.NPrf (syn_wfn (syn_chncodecutfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_lninteropfn
  have p0001 :=
    @g_ln1stfn
  have p0002 :=
    @g_ln1stfn
  have p0003 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0001 p0002
  have p0004 :=
    @g_fncross
  have p0005 :=
    @g_lninteropfn
  have p0006 :=
    @g_ln2ndfn
  have p0007 :=
    @g_ln1stfn
  have p0008 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0006 p0007
  have p0009 :=
    @g_lnimageopfn
  have p0010 :=
    @g_imageswapfn
  have p0011 :=
    @g_fnlndifop
  have p0012 :=
    @g_ln1stfn
  have p0013 :=
    @g_ln1stfn
  have p0014 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0012 p0013
  have p0015 :=
    @g_idex
  have p0016 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0014 p0017
  have p0019 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_inidm (syn_cvv)
  have p0022 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0021
  have p0023 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0020 p0022
  have p0024 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0011 p0023
  have p0025 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0026 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0025
  have p0027 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0024 p0026
  have p0028 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0010 p0027
  have p0029 :=
    @g_ln2ndfn
  have p0030 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0028 p0029
  have p0031 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_inidm (syn_cvv)
  have p0034 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0033
  have p0035 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0032 p0034
  have p0036 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0009 p0035
  have p0037 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0038 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0037
  have p0039 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0036 p0038
  have p0040 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0008 p0039
  have p0041 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0042 :=
    Nominal.mp p0040 p0041
  have p0043 :=
    @g_inidm (syn_cvv)
  have p0044 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0043
  have p0045 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0042 p0044
  have p0046 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0005 p0045
  have p0047 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0048 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0047
  have p0049 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0046 p0048
  have p0050 :=
    @g_lninteropfn
  have p0051 :=
    @g_ln2ndfn
  have p0052 :=
    @g_ln1stfn
  have p0053 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0051 p0052
  have p0054 :=
    @g_lnimageopfn
  have p0055 :=
    @g_imageswapfn
  have p0056 :=
    @g_fnlndifop
  have p0057 :=
    @g_ln1stfn
  have p0058 :=
    @g_ln1stfn
  have p0059 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0057 p0058
  have p0060 :=
    @g_idex
  have p0061 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0059 p0062
  have p0064 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_inidm (syn_cvv)
  have p0067 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0066
  have p0068 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0065 p0067
  have p0069 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0056 p0068
  have p0070 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0071 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0070
  have p0072 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0069 p0071
  have p0073 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0055 p0072
  have p0074 :=
    @g_ln2ndfn
  have p0075 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0073 p0074
  have p0076 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0077 :=
    Nominal.mp p0075 p0076
  have p0078 :=
    @g_inidm (syn_cvv)
  have p0079 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0078
  have p0080 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0077 p0079
  have p0081 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0054 p0080
  have p0082 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0083 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0082
  have p0084 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0081 p0083
  have p0085 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0053 p0084
  have p0086 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0087 :=
    Nominal.mp p0085 p0086
  have p0088 :=
    @g_inidm (syn_cvv)
  have p0089 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0088
  have p0090 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0087 p0089
  have p0091 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0050 p0090
  have p0092 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0093 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0092
  have p0094 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0091 p0093
  have p0095 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0049 p0094
  have p0096 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0097 :=
    Nominal.mp p0095 p0096
  have p0098 :=
    @g_inidm (syn_cvv)
  have p0099 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0098
  have p0100 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0097 p0099
  have p0101 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0004 p0100
  have p0102 :=
    (by simpa [syn_chncodesquarefn] using (Nominal.classEqRefl (syn_chncodesquarefn)))
  have p0103 :=
    @g_fneq1i (syn_cvv) (syn_chncodesquarefn) (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) p0102
  have p0104 :=
    @g_mpbir (syn_wfn (syn_chncodesquarefn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) (syn_cvv)) p0101 p0103
  have p0105 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodesquarefn) (syn_cvv)) p0003 p0104
  have p0106 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)
  have p0107 :=
    Nominal.mp p0105 p0106
  have p0108 :=
    @g_inidm (syn_cvv)
  have p0109 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0108
  have p0110 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv)) p0107 p0109
  have p0111 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0000 p0110
  have p0112 :=
    (by simpa [syn_chncoderelfn] using (Nominal.classEqRefl (syn_chncoderelfn)))
  have p0113 :=
    @g_fneq1i (syn_cvv) (syn_chncoderelfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) p0112
  have p0114 :=
    @g_mpbir (syn_wfn (syn_chncoderelfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cvv)) p0111 p0113
  have p0115 :=
    @g_lninteropfn
  have p0116 :=
    @g_ln2ndfn
  have p0117 :=
    @g_ln1stfn
  have p0118 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0116 p0117
  have p0119 :=
    @g_lnimageopfn
  have p0120 :=
    @g_imageswapfn
  have p0121 :=
    @g_fnlndifop
  have p0122 :=
    @g_ln1stfn
  have p0123 :=
    @g_ln1stfn
  have p0124 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0122 p0123
  have p0125 :=
    @g_idex
  have p0126 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0127 :=
    Nominal.mp p0125 p0126
  have p0128 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0124 p0127
  have p0129 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0130 :=
    Nominal.mp p0128 p0129
  have p0131 :=
    @g_inidm (syn_cvv)
  have p0132 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0131
  have p0133 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0130 p0132
  have p0134 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0121 p0133
  have p0135 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0136 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0135
  have p0137 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0134 p0136
  have p0138 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0120 p0137
  have p0139 :=
    @g_ln2ndfn
  have p0140 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0138 p0139
  have p0141 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0142 :=
    Nominal.mp p0140 p0141
  have p0143 :=
    @g_inidm (syn_cvv)
  have p0144 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0143
  have p0145 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0142 p0144
  have p0146 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0119 p0145
  have p0147 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0148 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0147
  have p0149 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0146 p0148
  have p0150 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0118 p0149
  have p0151 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0152 :=
    Nominal.mp p0150 p0151
  have p0153 :=
    @g_inidm (syn_cvv)
  have p0154 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0153
  have p0155 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0152 p0154
  have p0156 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0115 p0155
  have p0157 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0158 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0157
  have p0159 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0156 p0158
  have p0160 :=
    @g_pm3_2i (syn_wfn (syn_chncoderelfn) (syn_cvv)) (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0114 p0159
  have p0161 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncoderelfn) (syn_chncodecarrierfn)
  have p0162 :=
    Nominal.mp p0160 p0161
  have p0163 :=
    @g_inidm (syn_cvv)
  have p0164 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0163
  have p0165 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0162 p0164
  have p0166 :=
    (by simpa [syn_chncodecutfn] using (Nominal.classEqRefl (syn_chncodecutfn)))
  have p0167 :=
    @g_fneq1i (syn_cvv) (syn_chncodecutfn) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0166
  have p0168 :=
    @g_mpbir (syn_wfn (syn_chncodecutfn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0165 p0167
  exact p0168

#print axioms g_hncodecutfnfn

end NFChoice.DirectNominalPrf.WPPReplay
