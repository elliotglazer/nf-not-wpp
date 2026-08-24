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
import NominalWPPReplayChunk015Compact001Part039

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

noncomputable def g_wecutisoendpointseqclndv
    (B : Class) (C : Class) (D : Class) (R : Class) (H : Class) (hyp_wecutisoendpointseqclndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (.classEq B C)) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ H.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (.classEq B C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_D, fresh_y_not_C, fresh_y_not_H, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq B (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_ne_y, fresh_x_not_H, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))
  have p0001 :=
    @g_simpl (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wa (.classMem B D) (.classMem C D)) p0000 p0001
  have p0003 :=
    @g_simpl (.classMem B D) (.classMem C D)
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_wa (.classMem B D) (.classMem C D)) (.classMem B D) p0002 p0003
  have p0005 :=
    @g_elex B D
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (.classMem B D) (.classMem B (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_simpl (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))
  have p0008 :=
    @g_simpl (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wa (.classMem B D) (.classMem C D)) p0007 p0008
  have p0010 :=
    @g_simpr (.classMem B D) (.classMem C D)
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_wa (.classMem B D) (.classMem C D)) (.classMem C D) p0009 p0010
  have p0012 :=
    @g_elex C D
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (.classMem C D) (.classMem C (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0006 p0013
  have p0015 :=
    @g_eleq1 (.cv x) B D
  have p0016 :=
    @g_biid (.classMem (.cv y) D)
  have p0017 :=
    @g_a1i (syn_wb (.classMem (.cv y) D) (.classMem (.cv y) D)) (.classEq (.cv x) B) p0016
  have p0018 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D) (.classMem (.cv y) D) (.classMem (.cv y) D) p0015 p0017
  have p0019 :=
    @g_biid (.classMem H (syn_cvv))
  have p0020 :=
    @g_a1i (syn_wb (.classMem H (syn_cvv)) (.classMem H (syn_cvv))) (.classEq (.cv x) B) p0019
  have p0021 :=
    @g_anbi12d (.classEq (.cv x) B) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv)) (.classMem H (syn_cvv)) p0018 p0020
  have p0022 :=
    @g_sneq (.cv x) B
  have p0023 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid))) p0022
  have p0024 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0023
  have p0025 :=
    @g_sneq (.cv x) B
  have p0026 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid))) p0025
  have p0027 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0026
  have p0028 :=
    @g_xpeq12d (.classEq (.cv x) B) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) p0024 p0027
  have p0029 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) R p0028
  have p0030 :=
    @g_isoeq2 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) H
  have p0031 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))) (syn_wb (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0029 p0030
  have p0032 :=
    @g_sneq (.cv x) B
  have p0033 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid))) p0032
  have p0034 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0033
  have p0035 :=
    @g_isoeq4 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) H
  have p0036 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_wb (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0034 p0035
  have p0037 :=
    @g_bitrd (.classEq (.cv x) B) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0031 p0036
  have p0038 :=
    @g_anbi12d (.classEq (.cv x) B) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0021 p0037
  have p0039 :=
    @g_id (.classEq (.cv x) B)
  have p0040 :=
    @g_eqeq1d (.classEq (.cv x) B) (.cv x) B (.cv y) p0039
  have p0041 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (.cv x) (.cv y)) (.classEq B (.cv y)) p0038 p0040
  have p0042 :=
    @g_biid (.classMem B D)
  have p0043 :=
    @g_a1i (syn_wb (.classMem B D) (.classMem B D)) (.classEq (.cv y) C) p0042
  have p0044 :=
    @g_eleq1 (.cv y) C D
  have p0045 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem B D) (.classMem B D) (.classMem (.cv y) D) (.classMem C D) p0043 p0044
  have p0046 :=
    @g_biid (.classMem H (syn_cvv))
  have p0047 :=
    @g_a1i (syn_wb (.classMem H (syn_cvv)) (.classMem H (syn_cvv))) (.classEq (.cv y) C) p0046
  have p0048 :=
    @g_anbi12d (.classEq (.cv y) C) (syn_wa (.classMem B D) (.classMem (.cv y) D)) (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv)) (.classMem H (syn_cvv)) p0045 p0047
  have p0049 :=
    @g_sneq (.cv y) C
  have p0050 :=
    @g_imaeq2d (.classEq (.cv y) C) (syn_csn (.cv y)) (syn_csn C) (syn_ccnv (syn_cdif R (syn_cid))) p0049
  have p0051 :=
    @g_ineq2d (.classEq (.cv y) C) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)) D p0050
  have p0052 :=
    @g_sneq (.cv y) C
  have p0053 :=
    @g_imaeq2d (.classEq (.cv y) C) (syn_csn (.cv y)) (syn_csn C) (syn_ccnv (syn_cdif R (syn_cid))) p0052
  have p0054 :=
    @g_ineq2d (.classEq (.cv y) C) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)) D p0053
  have p0055 :=
    @g_xpeq12d (.classEq (.cv y) C) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) p0051 p0054
  have p0056 :=
    @g_ineq2d (.classEq (.cv y) C) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))) R p0055
  have p0057 :=
    @g_isoeq3 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) H
  have p0058 :=
    @g_syl (.classEq (.cv y) C) (.classEq (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))))) (syn_wb (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0056 p0057
  have p0059 :=
    @g_sneq (.cv y) C
  have p0060 :=
    @g_imaeq2d (.classEq (.cv y) C) (syn_csn (.cv y)) (syn_csn C) (syn_ccnv (syn_cdif R (syn_cid))) p0059
  have p0061 :=
    @g_ineq2d (.classEq (.cv y) C) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)) D p0060
  have p0062 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) H
  have p0063 :=
    @g_syl (.classEq (.cv y) C) (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))) (syn_wb (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) p0061 p0062
  have p0064 :=
    @g_bitrd (.classEq (.cv y) C) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))) p0058 p0063
  have p0065 :=
    @g_anbi12d (.classEq (.cv y) C) (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C)))) p0048 p0064
  have p0066 :=
    @g_id (.classEq (.cv y) C)
  have p0067 :=
    @g_eqeq2d (.classEq (.cv y) C) (.cv y) C B p0066
  have p0068 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (.classEq B (.cv y)) (.classEq B C) p0065 p0067
  have p0069 :=
    @g_wecutisoendpointseqndv x y D R H hyp_wecutisoendpointseqclndv_1
  have p0070 :=
    @g_vtocl2g (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (.cv x) (.cv y))) (.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq B (.cv y))) (.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (.classEq B C)) x y B C (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0041 p0068 p0069
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.imp (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (.classEq B C)) p0014 p0070
  have p0072 :=
    @g_pm2_43i (syn_wa (syn_wa (syn_wa (.classMem B D) (.classMem C D)) (.classMem H (syn_cvv))) (syn_wiso H (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn C))))) (.classEq B C) p0071
  exact p0072

noncomputable def g_strictsegdifiniclndv
    (B : Class) (D : Class) (R : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_cvv)) (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn B)))) := by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn B)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, fresh_x_not_R, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_sneq (.cv x) B
  have p0001 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid))) p0000
  have p0002 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0001
  have p0003 :=
    @g_sneq (.cv x) B
  have p0004 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ccnv R) p0003
  have p0005 :=
    @g_ineq2d (.classEq (.cv x) B) (syn_cima (syn_ccnv R) (syn_csn (.cv x))) (syn_cima (syn_ccnv R) (syn_csn B)) D p0004
  have p0006 :=
    @g_sneq (.cv x) B
  have p0007 :=
    @g_difeq12d (.classEq (.cv x) B) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn (.cv x)) (syn_csn B) p0005 p0006
  have p0008 :=
    @g_eqeq12d (.classEq (.cv x) B) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn B)) p0002 p0007
  have p0009 :=
    @g_strictsegdifinindv x D R
  have p0010 :=
    @g_vtoclg (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn B))) (syn_csn B))) x B (syn_cvv) dv_cache_0001 dv_cache_0002 p0008 p0009
  exact p0010

noncomputable def g_isostrictsegimandv
    (x : Var) (D : Class) (R : Class) (S : Class) (E : Class) (H : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (.classEq (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ H.fv
  have p0000 :=
    @g_strictsegdifinindv x D R
  have p0001 :=
    @g_a1i (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) p0000
  have p0002 :=
    @g_imaeq2d (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x))) H p0001
  have p0003 :=
    @g_simpl (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0004 :=
    @g_isof1o D E R S H
  have p0005 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso H R S D E) (syn_wf1o H D E) p0003 p0004
  have p0006 :=
    @g_f1ocnv D E H
  have p0007 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o H D E) (syn_wf1o (syn_ccnv H) E D) p0005 p0006
  have p0008 :=
    @g_f1ofun E D (syn_ccnv H)
  have p0009 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o (syn_ccnv H) E D) (syn_wfun (syn_ccnv H)) p0007 p0008
  have p0010 :=
    @g_imadif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)) H
  have p0011 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wfun (syn_ccnv H)) (.classEq (syn_cima H (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cdif (syn_cima H (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_cima H (syn_csn (.cv x))))) p0009 p0010
  have p0012 :=
    @g_eqtrd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cima H (syn_cdif (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x)))) (syn_csn (.cv x)))) (syn_cdif (syn_cima H (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_cima H (syn_csn (.cv x)))) p0002 p0011
  have p0013 :=
    @g_isoini D E (.cv x) R S H
  have p0014 :=
    @g_simpl (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0015 :=
    @g_isof1o D E R S H
  have p0016 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso H R S D E) (syn_wf1o H D E) p0014 p0015
  have p0017 :=
    @g_f1ofn D E H
  have p0018 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o H D E) (syn_wfn H D) p0016 p0017
  have p0019 :=
    @g_simpr (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0020 :=
    @g_jca (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wfn H D) (.classMem (.cv x) D) p0018 p0019
  have p0021 :=
    @g_fnsnfv D (.cv x) H
  have p0022 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (.classEq (syn_csn (syn_cfv H (.cv x))) (syn_cima H (syn_csn (.cv x)))) p0020 p0021
  have p0023 :=
    @g_eqcomd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_csn (syn_cfv H (.cv x))) (syn_cima H (syn_csn (.cv x))) p0022
  have p0024 :=
    @g_difeq12d (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_cima H (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x))))) (syn_cima H (syn_csn (.cv x))) (syn_csn (syn_cfv H (.cv x))) p0013 p0023
  have p0025 :=
    @g_eqtrd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cdif (syn_cima H (syn_cin D (syn_cima (syn_ccnv R) (syn_csn (.cv x))))) (syn_cima H (syn_csn (.cv x)))) (syn_cdif (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x))))) (syn_csn (syn_cfv H (.cv x)))) p0012 p0024
  have p0026 :=
    @g_simpl (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0027 :=
    @g_isof1o D E R S H
  have p0028 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso H R S D E) (syn_wf1o H D E) p0026 p0027
  have p0029 :=
    @g_f1of D E H
  have p0030 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf1o H D E) (syn_wf H D E) p0028 p0029
  have p0031 :=
    @g_simpr (syn_wiso H R S D E) (.classMem (.cv x) D)
  have p0032 :=
    @g_jca (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wf H D E) (.classMem (.cv x) D) p0030 p0031
  have p0033 :=
    @g_ffvelrn D E (.cv x) H
  have p0034 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wa (syn_wf H D E) (.classMem (.cv x) D)) (.classMem (syn_cfv H (.cv x)) E) p0032 p0033
  have p0035 :=
    @g_elex (syn_cfv H (.cv x)) E
  have p0036 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (.classMem (syn_cfv H (.cv x)) E) (.classMem (syn_cfv H (.cv x)) (syn_cvv)) p0034 p0035
  have p0037 :=
    @g_strictsegdifiniclndv (syn_cfv H (.cv x)) E S
  have p0038 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (.classMem (syn_cfv H (.cv x)) (syn_cvv)) (.classEq (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cdif (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x))))) (syn_csn (syn_cfv H (.cv x))))) p0036 p0037
  have p0039 :=
    @g_eqcomd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cdif (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x))))) (syn_csn (syn_cfv H (.cv x)))) p0038
  have p0040 :=
    @g_eqtrd (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_cima H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cdif (syn_cin E (syn_cima (syn_ccnv S) (syn_csn (syn_cfv H (.cv x))))) (syn_csn (syn_cfv H (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) p0025 p0039
  exact p0040

#print axioms g_isostrictsegimandv

end NFChoice.DirectNominalPrf.WPPReplay
