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
import NominalWPPReplayChunk012BCompact001Part006

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

noncomputable def g_f1oiso2
    (x : Var) (y : Var) (A : Class) (B : Class) (R : Class) (S : Class) (H : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) (hyp_f1oiso2_1 : Nominal.NPrf (.classEq S (syn_copab x y (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))))) :
    Nominal.NPrf (.imp (syn_wf1o H A B) (syn_wiso H R S A B)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ S.fv ∪ H.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_H : z ∉ H.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_S : w ∉ S.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_H : w ∉ H.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : w ∉ ((syn_cfv (syn_ccnv H) (.cv y))).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_H, fresh_w_ne_y, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Wff.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_x, fresh_w_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cfv (syn_ccnv H) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, fresh_z_not_H, fresh_z_ne_y, fresh_z_ne_w, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_B, fresh_z_ne_y, fresh_z_not_H, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_B, fresh_w_ne_y, fresh_w_not_H, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_wf1o H A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((syn_wf1o H A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_not_B, fresh_w_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0013 : x ∉ ((syn_wf1o H A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, dv_H_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_wf1o H A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, dv_H_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_H_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : w ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ (H).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_H_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : w ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0028 : y ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0029 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0030 : z ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0031 : w ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have p0000 :=
    @g_f1ocnvdm A B (.cv x) H
  have p0001 :=
    @g_adantrr (syn_wf1o H A B) (.classMem (.cv x) B) (.classMem (syn_cfv (syn_ccnv H) (.cv x)) A) (.classMem (.cv y) B) p0000
  have p0002 :=
    @g_n_3adant3 (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (syn_cfv (syn_ccnv H) (.cv x)) A) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0001
  have p0003 :=
    @g_f1ocnvdm A B (.cv y) H
  have p0004 :=
    @g_adantrl (syn_wf1o H A B) (.classMem (.cv y) B) (.classMem (syn_cfv (syn_ccnv H) (.cv y)) A) (.classMem (.cv x) B) p0003
  have p0005 :=
    @g_n_3adant3 (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (syn_cfv (syn_ccnv H) (.cv y)) A) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0004
  have p0006 :=
    @g_f1ocnvfv2 A B (.cv x) H
  have p0007 :=
    @g_eqcomd (syn_wa (syn_wf1o H A B) (.classMem (.cv x) B)) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))) (.cv x) p0006
  have p0008 :=
    @g_f1ocnvfv2 A B (.cv y) H
  have p0009 :=
    @g_eqcomd (syn_wa (syn_wf1o H A B) (.classMem (.cv y) B)) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))) (.cv y) p0008
  have p0010 :=
    @g_anim12dan (syn_wf1o H A B) (.classMem (.cv x) B) (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classMem (.cv y) B) (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y)))) p0007 p0009
  have p0011 :=
    @g_n_3adant3 (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0010
  have p0012 :=
    @g_simp3 (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))
  have p0013 :=
    @g_fveq2 (.cv w) (syn_cfv (syn_ccnv H) (.cv y)) H
  have p0014 :=
    @g_eqeq2d (.classEq (.cv w) (syn_cfv (syn_ccnv H) (.cv y))) (syn_cfv H (.cv w)) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))) (.cv y) p0013
  have p0015 :=
    @g_anbi2d (.classEq (.cv w) (syn_cfv (syn_ccnv H) (.cv y))) (.classEq (.cv y) (syn_cfv H (.cv w))) (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y)))) (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) p0014
  have p0016 :=
    @g_breq2 (.cv w) (syn_cfv (syn_ccnv H) (.cv y)) (syn_cfv (syn_ccnv H) (.cv x)) R
  have p0017 :=
    @g_anbi12d (.classEq (.cv w) (syn_cfv (syn_ccnv H) (.cv y))) (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0015 p0016
  have p0018 :=
    @g_rspcev (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w))) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))) w (syn_cfv (syn_ccnv H) (.cv y)) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0017
  have p0019 :=
    @g_syl12anc (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))) (.classMem (syn_cfv (syn_ccnv H) (.cv y)) A) (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv y))))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w)))) p0005 p0011 p0012 p0018
  have p0020 :=
    @g_fveq2 (.cv z) (syn_cfv (syn_ccnv H) (.cv x)) H
  have p0021 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x))) (syn_cfv H (.cv z)) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x))) (.cv x) p0020
  have p0022 :=
    @g_anbi1d (.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x))) (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (.cv w))) p0021
  have p0023 :=
    @g_breq1 (.cv z) (syn_cfv (syn_ccnv H) (.cv x)) (.cv w) R
  have p0024 :=
    @g_anbi12d (.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x))) (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w)) p0022 p0023
  have p0025 :=
    @g_rexbidv (.classEq (.cv z) (syn_cfv (syn_ccnv H) (.cv x))) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w))) w A dv_cache_0004 p0024
  have p0026 :=
    @g_rspcev (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w)))) z (syn_cfv (syn_ccnv H) (.cv x)) A dv_cache_0005 dv_cache_0006 dv_cache_0007 p0025
  have p0027 :=
    @g_syl2anc (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))) (.classMem (syn_cfv (syn_ccnv H) (.cv x)) A) (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (syn_cfv (syn_ccnv H) (.cv x)))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (.cv w)))) (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))))) p0002 p0019 p0026
  have p0028 :=
    @g_n_3expib (syn_wf1o H A B) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))))) p0027
  have p0029 :=
    @g_simp3ll (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))) (syn_wbr (.cv z) R (.cv w)) (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A))
  have p0030 :=
    @g_simp1 (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))
  have p0031 :=
    @g_simp2l (syn_wf1o H A B) (.classMem (.cv z) A) (.classMem (.cv w) A) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))
  have p0032 :=
    @g_f1of A B H
  have p0033 :=
    @g_ffvelrn A B (.cv z) H
  have p0034 :=
    @g_sylan (syn_wf1o H A B) (syn_wf H A B) (.classMem (.cv z) A) (.classMem (syn_cfv H (.cv z)) B) p0032 p0033
  have p0035 :=
    @g_syl2anc (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (syn_wf1o H A B) (.classMem (.cv z) A) (.classMem (syn_cfv H (.cv z)) B) p0030 p0031 p0034
  have p0036 :=
    @g_eqeltrd (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (.cv x) (syn_cfv H (.cv z)) B p0029 p0035
  have p0037 :=
    @g_simp3lr (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w))) (syn_wbr (.cv z) R (.cv w)) (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A))
  have p0038 :=
    @g_simp2r (syn_wf1o H A B) (.classMem (.cv z) A) (.classMem (.cv w) A) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))
  have p0039 :=
    @g_ffvelrn A B (.cv w) H
  have p0040 :=
    @g_sylan (syn_wf1o H A B) (syn_wf H A B) (.classMem (.cv w) A) (.classMem (syn_cfv H (.cv w)) B) p0032 p0039
  have p0041 :=
    @g_syl2anc (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (syn_wf1o H A B) (.classMem (.cv w) A) (.classMem (syn_cfv H (.cv w)) B) p0030 p0038 p0040
  have p0042 :=
    @g_eqeltrd (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (.cv y) (syn_cfv H (.cv w)) B p0037 p0041
  have p0043 :=
    @g_simp3r (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))
  have p0044 :=
    @g_eqcomd (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (.cv x) (syn_cfv H (.cv z)) p0029
  have p0045 :=
    @g_f1ocnvfv A B (.cv z) (.cv x) H
  have p0046 :=
    @g_syl2anc (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (syn_wf1o H A B) (.classMem (.cv z) A) (.imp (.classEq (syn_cfv H (.cv z)) (.cv x)) (.classEq (syn_cfv (syn_ccnv H) (.cv x)) (.cv z))) p0030 p0031 p0045
  have p0047 :=
    @g_mpd (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (.classEq (syn_cfv H (.cv z)) (.cv x)) (.classEq (syn_cfv (syn_ccnv H) (.cv x)) (.cv z)) p0044 p0046
  have p0048 :=
    @g_eqcomd (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (.cv y) (syn_cfv H (.cv w)) p0037
  have p0049 :=
    @g_f1ocnvfv A B (.cv w) (.cv y) H
  have p0050 :=
    @g_syl2anc (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (syn_wf1o H A B) (.classMem (.cv w) A) (.imp (.classEq (syn_cfv H (.cv w)) (.cv y)) (.classEq (syn_cfv (syn_ccnv H) (.cv y)) (.cv w))) p0030 p0038 p0049
  have p0051 :=
    @g_mpd (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (.classEq (syn_cfv H (.cv w)) (.cv y)) (.classEq (syn_cfv (syn_ccnv H) (.cv y)) (.cv w)) p0048 p0050
  have p0052 :=
    @g_n_3brtr4d (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (.cv z) (.cv w) (syn_cfv (syn_ccnv H) (.cv x)) (syn_cfv (syn_ccnv H) (.cv y)) R p0043 p0047 p0051
  have p0053 :=
    @g_jca31 (syn_w3a (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))) (.classMem (.cv x) B) (.classMem (.cv y) B) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))) p0036 p0042 p0052
  have p0054 :=
    @g_n_3exp (syn_wf1o H A B) (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) A)) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))) (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))) p0053
  have p0055 :=
    @g_rexlimdvv (syn_wf1o H A B) (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))) (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))) z w A A dv_cache_0002 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0054
  have p0056 :=
    @g_impbid (syn_wf1o H A B) (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))) (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))))) p0028 p0055
  have p0057 :=
    @g_opabbidv (syn_wf1o H A B) (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y)))) (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))))) x y dv_cache_0013 dv_cache_0014 p0056
  have p0058 :=
    @g_syl5eq (syn_wf1o H A B) S (syn_copab x y (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (syn_cfv (syn_ccnv H) (.cv x)) R (syn_cfv (syn_ccnv H) (.cv y))))) (syn_copab x y (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w)))))) hyp_f1oiso2_1 p0057
  have p0059 :=
    @g_f1oiso z w x y A B R S H dv_cache_0015 dv_cache_0006 dv_cache_0002 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0012 dv_cache_0030 dv_cache_0031
  have p0060 :=
    @g_mpdan (syn_wf1o H A B) (.classEq S (syn_copab x y (syn_wrex z A (syn_wrex w A (syn_wa (syn_wa (.classEq (.cv x) (syn_cfv H (.cv z))) (.classEq (.cv y) (syn_cfv H (.cv w)))) (syn_wbr (.cv z) R (.cv w))))))) (syn_wiso H R S A B) p0058 p0059
  exact p0060

noncomputable def g_opbr1st
    (A : Class) (B : Class) (C : Class) (hyp_opbr1st_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_opbr1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_cop A B) (syn_c1st) C) (.classEq A C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((syn_cop A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wbr (syn_cop A B) (syn_c1st) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq A C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex (syn_cop A B) C (syn_c1st)
  have p0001 :=
    @g_simprd (syn_wbr (syn_cop A B) (syn_c1st) C) (.classMem (syn_cop A B) (syn_cvv)) (.classMem C (syn_cvv)) p0000
  have p0002 :=
    @g_eleq1 A C (syn_cvv)
  have p0003 :=
    @g_mpbii (.classEq A C) (.classMem A (syn_cvv)) (.classMem C (syn_cvv)) hyp_opbr1st_1 p0002
  have p0004 :=
    @g_breq2 (.cv x) C (syn_cop A B) (syn_c1st)
  have p0005 :=
    @g_eqeq2 (.cv x) C A
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_br1st y (syn_cop A B) (.cv x) dv_cache_0001 dv_cache_0002 p0006
  have p0008 :=
    @g_biidd (.classEq (.cv y) B) (.classEq (.cv x) A)
  have p0009 :=
    @g_ceqsexv (.classEq (.cv x) A) (.classEq (.cv x) A) y B dv_cache_0003 dv_cache_0004 hyp_opbr1st_2 p0008
  have p0010 :=
    @g_eqcom (syn_cop A B) (syn_cop (.cv x) (.cv y))
  have p0011 :=
    @g_opth (.cv x) (.cv y) A B
  have p0012 :=
    @g_ancom (.classEq (.cv x) A) (.classEq (.cv y) B)
  have p0013 :=
    @g_bitri (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B)) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wa (.classEq (.cv y) B) (.classEq (.cv x) A)) p0011 p0012
  have p0014 :=
    @g_bitri (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B)) (syn_wa (.classEq (.cv y) B) (.classEq (.cv x) A)) p0010 p0013
  have p0015 :=
    @g_exbii (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) (syn_wa (.classEq (.cv y) B) (.classEq (.cv x) A)) y p0014
  have p0016 :=
    @g_eqcom A (.cv x)
  have p0017 :=
    @g_n_3bitr4i (syn_wex y (syn_wa (.classEq (.cv y) B) (.classEq (.cv x) A))) (.classEq (.cv x) A) (syn_wex y (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))) (.classEq A (.cv x)) p0009 p0015 p0016
  have p0018 :=
    @g_bitri (syn_wbr (syn_cop A B) (syn_c1st) (.cv x)) (syn_wex y (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))) (.classEq A (.cv x)) p0007 p0017
  have p0019 :=
    @g_vtoclbg (syn_wbr (syn_cop A B) (syn_c1st) (.cv x)) (.classEq A (.cv x)) (syn_wbr (syn_cop A B) (syn_c1st) C) (.classEq A C) x C (syn_cvv) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0004 p0005 p0018
  have p0020 :=
    @g_pm5_21nii (syn_wbr (syn_cop A B) (syn_c1st) C) (.classMem C (syn_cvv)) (.classEq A C) p0001 p0003 p0019
  exact p0020

noncomputable def g_opbr2nd
    (A : Class) (B : Class) (C : Class) (hyp_opbr1st_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_opbr1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_cop A B) (syn_c2nd) C) (.classEq B C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((syn_cop A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv x) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wbr (syn_cop A B) (syn_c2nd) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq B C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex (syn_cop A B) C (syn_c2nd)
  have p0001 :=
    @g_simprd (syn_wbr (syn_cop A B) (syn_c2nd) C) (.classMem (syn_cop A B) (syn_cvv)) (.classMem C (syn_cvv)) p0000
  have p0002 :=
    @g_eleq1 B C (syn_cvv)
  have p0003 :=
    @g_mpbii (.classEq B C) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) hyp_opbr1st_2 p0002
  have p0004 :=
    @g_breq2 (.cv x) C (syn_cop A B) (syn_c2nd)
  have p0005 :=
    @g_eqeq2 (.cv x) C B
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_br2nd y (syn_cop A B) (.cv x) dv_cache_0001 dv_cache_0002 p0006
  have p0008 :=
    @g_biidd (.classEq (.cv y) A) (.classEq (.cv x) B)
  have p0009 :=
    @g_ceqsexv (.classEq (.cv x) B) (.classEq (.cv x) B) y A dv_cache_0003 dv_cache_0004 hyp_opbr1st_1 p0008
  have p0010 :=
    @g_eqcom (syn_cop A B) (syn_cop (.cv y) (.cv x))
  have p0011 :=
    @g_opth (.cv y) (.cv x) A B
  have p0012 :=
    @g_bitri (.classEq (syn_cop A B) (syn_cop (.cv y) (.cv x))) (.classEq (syn_cop (.cv y) (.cv x)) (syn_cop A B)) (syn_wa (.classEq (.cv y) A) (.classEq (.cv x) B)) p0010 p0011
  have p0013 :=
    @g_exbii (.classEq (syn_cop A B) (syn_cop (.cv y) (.cv x))) (syn_wa (.classEq (.cv y) A) (.classEq (.cv x) B)) y p0012
  have p0014 :=
    @g_eqcom B (.cv x)
  have p0015 :=
    @g_n_3bitr4i (syn_wex y (syn_wa (.classEq (.cv y) A) (.classEq (.cv x) B))) (.classEq (.cv x) B) (syn_wex y (.classEq (syn_cop A B) (syn_cop (.cv y) (.cv x)))) (.classEq B (.cv x)) p0009 p0013 p0014
  have p0016 :=
    @g_bitri (syn_wbr (syn_cop A B) (syn_c2nd) (.cv x)) (syn_wex y (.classEq (syn_cop A B) (syn_cop (.cv y) (.cv x)))) (.classEq B (.cv x)) p0007 p0015
  have p0017 :=
    @g_vtoclbg (syn_wbr (syn_cop A B) (syn_c2nd) (.cv x)) (.classEq B (.cv x)) (syn_wbr (syn_cop A B) (syn_c2nd) C) (.classEq B C) x C (syn_cvv) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0004 p0005 p0016
  have p0018 :=
    @g_pm5_21nii (syn_wbr (syn_cop A B) (syn_c2nd) C) (.classMem C (syn_cvv)) (.classEq B C) p0001 p0003 p0017
  exact p0018

#print axioms g_opbr2nd

end NFChoice.DirectNominalPrf.WPPReplay
