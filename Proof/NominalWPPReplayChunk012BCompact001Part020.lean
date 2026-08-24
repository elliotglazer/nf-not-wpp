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
import NominalWPPReplayChunk012BCompact001Part019

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

noncomputable def g_trtxp
    (A : Class) (B : Class) (C : Class) (R : Class) (S : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr A R B) (syn_wbr A S C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_R : t ∉ R.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_S : t ∉ S.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have dv_cache_0001 : t ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_ccnv (syn_c1st))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_wbr (.cv x) R (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_ccnv (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((syn_wbr (.cv x) S (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_z, fresh_t_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_B, fresh_z_not_C, fresh_z_not_R, fresh_z_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B (.cv z))) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, fresh_y_ne_z, fresh_y_not_R, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((Wff.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr A R B) (syn_wbr A S C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, fresh_x_not_R, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex A (syn_cop B C) (syn_ctxp R S)
  have p0001 :=
    @g_opexb B C
  have p0002 :=
    @g_anbi2i (.classMem (syn_cop B C) (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem A (syn_cvv)) p0001
  have p0003 :=
    @g_sylib (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (.classMem A (syn_cvv)) (.classMem (syn_cop B C) (syn_cvv))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))) p0000 p0002
  have p0004 :=
    @g_brex A B R
  have p0005 :=
    @g_brex A C S
  have p0006 :=
    @g_anim12i (syn_wbr A R B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr A S C) (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv))) p0004 p0005
  have p0007 :=
    @g_anandi (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0008 :=
    @g_sylibr (syn_wa (syn_wbr A R B) (syn_wbr A S C)) (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv)))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))) p0006 p0007
  have p0009 :=
    @g_breq1 (.cv x) A (syn_cop B C) (syn_ctxp R S)
  have p0010 :=
    @g_breq1 (.cv x) A B R
  have p0011 :=
    @g_breq1 (.cv x) A C S
  have p0012 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wbr (.cv x) R B) (syn_wbr A R B) (syn_wbr (.cv x) S C) (syn_wbr A S C) p0010 p0011
  have p0013 :=
    @g_bibi12d (.classEq (.cv x) A) (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C)) (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C)) (syn_wa (syn_wbr A R B) (syn_wbr A S C)) p0009 p0012
  have p0014 :=
    @g_imbi2d (.classEq (.cv x) A) (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C))) (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr A R B) (syn_wbr A S C))) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) p0013
  have p0015 :=
    @g_opeq1 (.cv y) B (.cv z)
  have p0016 :=
    @g_breq2d (.classEq (.cv y) B) (syn_cop (.cv y) (.cv z)) (syn_cop B (.cv z)) (.cv x) (syn_ctxp R S) p0015
  have p0017 :=
    @g_breq2 (.cv y) B (.cv x) R
  have p0018 :=
    @g_anbi1d (.classEq (.cv y) B) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S (.cv z)) p0017
  have p0019 :=
    @g_bibi12d (.classEq (.cv y) B) (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B (.cv z))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S (.cv z))) p0016 p0018
  have p0020 :=
    @g_opeq2 (.cv z) C B
  have p0021 :=
    @g_breq2d (.classEq (.cv z) C) (syn_cop B (.cv z)) (syn_cop B C) (.cv x) (syn_ctxp R S) p0020
  have p0022 :=
    @g_breq2 (.cv z) C (.cv x) S
  have p0023 :=
    @g_anbi2d (.classEq (.cv z) C) (syn_wbr (.cv x) S (.cv z)) (syn_wbr (.cv x) S C) (syn_wbr (.cv x) R B) p0022
  have p0024 :=
    @g_bibi12d (.classEq (.cv z) C) (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B (.cv z))) (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S (.cv z))) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C)) p0021 p0023
  have p0025 :=
    (by simpa [syn_ctxp] using (Nominal.classEqRefl (syn_ctxp R S)))
  have p0026 :=
    @g_breqi (.cv x) (syn_cop (.cv y) (.cv z)) (syn_ctxp R S) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)) p0025
  have p0027 :=
    @g_brin (.cv x) (syn_cop (.cv y) (.cv z)) (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)
  have p0028 :=
    @g_brco t (.cv x) (syn_cop (.cv y) (.cv z)) (syn_ccnv (syn_c1st)) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0029 :=
    @g_ancom (syn_wbr (.cv x) R (.cv t)) (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z)))
  have p0030 :=
    @g_brcnv (.cv t) (syn_cop (.cv y) (.cv z)) (syn_c1st)
  have p0031 :=
    @g_vex y
  have p0032 :=
    @g_vex z
  have p0033 :=
    @g_opbr1st (.cv y) (.cv z) (.cv t) p0031 p0032
  have p0034 :=
    @g_equcom y t
  have p0035_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv y) (.cv z)) (syn_c1st) (.cv t)) (.objEq y t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_c1st syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0033
  have p0035 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z))) (syn_wbr (syn_cop (.cv y) (.cv z)) (syn_c1st) (.cv t)) (.objEq y t) (.objEq t y) p0030 p0035_e01_recanon p0034
  have p0036 :=
    @g_anbi1i (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z))) (.objEq t y) (syn_wbr (.cv x) R (.cv t)) p0035
  have p0037 :=
    @g_bitri (syn_wa (syn_wbr (.cv x) R (.cv t)) (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z)))) (syn_wa (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv t))) (syn_wa (.objEq t y) (syn_wbr (.cv x) R (.cv t))) p0029 p0036
  have p0038 :=
    @g_exbii (syn_wa (syn_wbr (.cv x) R (.cv t)) (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z)))) (syn_wa (.objEq t y) (syn_wbr (.cv x) R (.cv t))) t p0037
  have p0039 :=
    @g_breq2 (.cv t) (.cv y) (.cv x) R
  have p0040 :=
    @g_ceqsexv (syn_wbr (.cv x) R (.cv t)) (syn_wbr (.cv x) R (.cv y)) t (.cv y) dv_cache_0005 dv_cache_0006 p0031 p0039
  have p0041_e02_recanon : Nominal.NPrf (syn_wb (syn_wex t (syn_wa (.objEq t y) (syn_wbr (.cv x) R (.cv t)))) (syn_wbr (.cv x) R (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0040
  have p0041 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_cop (.cv y) (.cv z))) (syn_wex t (syn_wa (syn_wbr (.cv x) R (.cv t)) (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z))))) (syn_wex t (syn_wa (.objEq t y) (syn_wbr (.cv x) R (.cv t)))) (syn_wbr (.cv x) R (.cv y)) p0028 p0038 p0041_e02_recanon
  have p0042 :=
    @g_brco t (.cv x) (syn_cop (.cv y) (.cv z)) (syn_ccnv (syn_c2nd)) S dv_cache_0001 dv_cache_0002 dv_cache_0007 dv_cache_0008
  have p0043 :=
    @g_ancom (syn_wbr (.cv x) S (.cv t)) (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z)))
  have p0044 :=
    @g_brcnv (.cv t) (syn_cop (.cv y) (.cv z)) (syn_c2nd)
  have p0045 :=
    @g_opbr2nd (.cv y) (.cv z) (.cv t) p0031 p0032
  have p0046 :=
    @g_equcom z t
  have p0047_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv y) (.cv z)) (syn_c2nd) (.cv t)) (.objEq z t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_c2nd syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0045
  have p0047 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z))) (syn_wbr (syn_cop (.cv y) (.cv z)) (syn_c2nd) (.cv t)) (.objEq z t) (.objEq t z) p0044 p0047_e01_recanon p0046
  have p0048 :=
    @g_anbi1i (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z))) (.objEq t z) (syn_wbr (.cv x) S (.cv t)) p0047
  have p0049 :=
    @g_bitri (syn_wa (syn_wbr (.cv x) S (.cv t)) (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z)))) (syn_wa (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) S (.cv t))) (syn_wa (.objEq t z) (syn_wbr (.cv x) S (.cv t))) p0043 p0048
  have p0050 :=
    @g_exbii (syn_wa (syn_wbr (.cv x) S (.cv t)) (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z)))) (syn_wa (.objEq t z) (syn_wbr (.cv x) S (.cv t))) t p0049
  have p0051 :=
    @g_breq2 (.cv t) (.cv z) (.cv x) S
  have p0052 :=
    @g_ceqsexv (syn_wbr (.cv x) S (.cv t)) (syn_wbr (.cv x) S (.cv z)) t (.cv z) dv_cache_0009 dv_cache_0010 p0032 p0051
  have p0053_e02_recanon : Nominal.NPrf (syn_wb (syn_wex t (syn_wa (.objEq t z) (syn_wbr (.cv x) S (.cv t)))) (syn_wbr (.cv x) S (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0052
  have p0053 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c2nd)) S) (syn_cop (.cv y) (.cv z))) (syn_wex t (syn_wa (syn_wbr (.cv x) S (.cv t)) (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z))))) (syn_wex t (syn_wa (.objEq t z) (syn_wbr (.cv x) S (.cv t)))) (syn_wbr (.cv x) S (.cv z)) p0042 p0050 p0053_e02_recanon
  have p0054 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c2nd)) S) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) S (.cv z)) p0041 p0053
  have p0055 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)) (syn_cop (.cv y) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c2nd)) S) (syn_cop (.cv y) (.cv z)))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) p0026 p0027 p0054
  have p0056 :=
    @g_vtocl2g (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop (.cv y) (.cv z))) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))) (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B (.cv z))) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S (.cv z)))) (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C))) y z B C (syn_cvv) (syn_cvv) dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0019 p0024 p0055
  have p0057 :=
    @g_vtoclg (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C)))) (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr A R B) (syn_wbr A S C)))) x A (syn_cvv) dv_cache_0016 dv_cache_0017 p0014 p0056
  have p0058 :=
    @g_imp (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr A R B) (syn_wbr A S C))) p0057
  have p0059 :=
    @g_pm5_21nii (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))) (syn_wa (syn_wbr A R B) (syn_wbr A S C)) p0003 p0008 p0058
  exact p0059

noncomputable def g_oteltxp
    (A : Class) (B : Class) (C : Class) (R : Class) (S : Class) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop A (syn_cop B C)) (syn_ctxp R S)) (syn_wa (.classMem (syn_cop A B) R) (.classMem (syn_cop A C) S))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ S.fv
  have p0000 :=
    @g_trtxp A B C R S
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A (syn_ctxp R S) (syn_cop B C))))
  have p0002 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A R B)))
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A S C)))
  have p0004 :=
    @g_anbi12i (syn_wbr A R B) (.classMem (syn_cop A B) R) (syn_wbr A S C) (.classMem (syn_cop A C) S) p0002 p0003
  have p0005 :=
    @g_n_3bitr3i (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr A R B) (syn_wbr A S C)) (.classMem (syn_cop A (syn_cop B C)) (syn_ctxp R S)) (syn_wa (.classMem (syn_cop A B) R) (.classMem (syn_cop A C) S)) p0000 p0001 p0004
  exact p0005

#print axioms g_oteltxp

end NFChoice.DirectNominalPrf.WPPReplay
