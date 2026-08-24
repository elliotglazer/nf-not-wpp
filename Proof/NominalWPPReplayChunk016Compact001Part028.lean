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
import NominalWPPReplayChunk016Compact001Part027

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

noncomputable def g_wecutnclecclndv
    (A : Class) (B : Class) (D : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_wecutnclecclndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.imp (syn_w3a (.classMem A D) (.classMem B D) (syn_wbr A R B)) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.imp (syn_w3a (.classMem A D) (.classMem B D) (syn_wbr A R B)) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_R, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.imp (syn_w3a (.classMem A D) (.classMem (.cv y) D) (syn_wbr A R (.cv y))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv x) A)
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (.cv x) A D p0000
  have p0002 :=
    @g_id (.classEq (.cv x) A)
  have p0003 :=
    @g_breq1d (.classEq (.cv x) A) (.cv x) A (.cv y) R p0002
  have p0004 :=
    @g_n_3anbi13d (.classEq (.cv x) A) (.classMem (.cv x) D) (.classMem A D) (syn_wbr (.cv x) R (.cv y)) (syn_wbr A R (.cv y)) (.classMem (.cv y) D) p0001 p0003
  have p0005 :=
    @g_id (.classEq (.cv x) A)
  have p0006 :=
    @g_sneqd (.classEq (.cv x) A) (.cv x) A p0005
  have p0007 :=
    @g_imaeq2d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) (syn_ccnv (syn_cdif R (syn_cid))) p0006
  have p0008 :=
    @g_ineq2d (.classEq (.cv x) A) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)) D p0007
  have p0009 :=
    @g_nceqd (.classEq (.cv x) A) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))) p0008
  have p0010 :=
    @g_breq1d (.classEq (.cv x) A) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_clec) p0009
  have p0011 :=
    @g_imbi12d (.classEq (.cv x) A) (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (syn_w3a (.classMem A D) (.classMem (.cv y) D) (syn_wbr A R (.cv y))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0004 p0010
  have p0012 :=
    @g_id (.classEq (.cv y) B)
  have p0013 :=
    @g_eleq1d (.classEq (.cv y) B) (.cv y) B D p0012
  have p0014 :=
    @g_id (.classEq (.cv y) B)
  have p0015 :=
    @g_breq2d (.classEq (.cv y) B) (.cv y) B A R p0014
  have p0016 :=
    @g_n_3anbi23d (.classEq (.cv y) B) (.classMem (.cv y) D) (.classMem B D) (syn_wbr A R (.cv y)) (syn_wbr A R B) (.classMem A D) p0013 p0015
  have p0017 :=
    @g_id (.classEq (.cv y) B)
  have p0018 :=
    @g_sneqd (.classEq (.cv y) B) (.cv y) B p0017
  have p0019 :=
    @g_imaeq2d (.classEq (.cv y) B) (syn_csn (.cv y)) (syn_csn B) (syn_ccnv (syn_cdif R (syn_cid))) p0018
  have p0020 :=
    @g_ineq2d (.classEq (.cv y) B) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0019
  have p0021 :=
    @g_nceqd (.classEq (.cv y) B) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) p0020
  have p0022 :=
    @g_breq2d (.classEq (.cv y) B) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_clec) p0021
  have p0023 :=
    @g_imbi12d (.classEq (.cv y) B) (syn_w3a (.classMem A D) (.classMem (.cv y) D) (syn_wbr A R (.cv y))) (syn_w3a (.classMem A D) (.classMem B D) (syn_wbr A R B)) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) p0016 p0022
  have p0024 :=
    @g_wecutnclecndv x y D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 hyp_wecutnclecclndv_1
  have p0025 :=
    @g_vtocl2g (.imp (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (.imp (syn_w3a (.classMem A D) (.classMem (.cv y) D) (syn_wbr A R (.cv y))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (.imp (syn_w3a (.classMem A D) (.classMem B D) (syn_wbr A R B)) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))) x y A B (syn_cvv) (syn_cvv) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0011 p0023 p0024
  exact p0025

noncomputable def g_wecuttypedbrndv
    (y : Var) (z : Var) (D : Class) (R : Class) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wb (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_simpl (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
  have p0001 :=
    @g_pw12argcl (.cv y) D
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv y))) D) (.classEq (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))))) p0000 p0001
  have p0003 :=
    @g_simprd (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (syn_cuni (.cv y))) D) (.classEq (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y)))))) p0002
  have p0004 :=
    @g_simpr (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
  have p0005 :=
    @g_pw12argcl (.cv z) D
  have p0006 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv z))) D) (.classEq (.cv z) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z))))))) p0004 p0005
  have p0007 :=
    @g_simprd (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (syn_cuni (.cv z))) D) (.classEq (.cv z) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z)))))) p0006
  have p0008 :=
    @g_breq12d (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))) (.cv z) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z))))) (syn_csi (syn_csi R)) p0003 p0007
  have p0009 :=
    @g_snex (syn_cuni (syn_cuni (.cv y)))
  have p0010 :=
    @g_snex (syn_cuni (syn_cuni (.cv z)))
  have p0011 :=
    @g_brsnsi (syn_csn (syn_cuni (syn_cuni (.cv y)))) (syn_csn (syn_cuni (syn_cuni (.cv z)))) (syn_csi R) p0009 p0010
  have p0012 :=
    @g_vex y
  have p0013 :=
    @g_uniex (.cv y) p0012
  have p0014 :=
    @g_uniex (syn_cuni (.cv y)) p0013
  have p0015 :=
    @g_vex z
  have p0016 :=
    @g_uniex (.cv z) p0015
  have p0017 :=
    @g_uniex (syn_cuni (.cv z)) p0016
  have p0018 :=
    @g_brsnsi (syn_cuni (syn_cuni (.cv y))) (syn_cuni (syn_cuni (.cv z))) R p0014 p0017
  have p0019 :=
    @g_bitri (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))) (syn_csi (syn_csi R)) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z)))))) (syn_wbr (syn_csn (syn_cuni (syn_cuni (.cv y)))) (syn_csi R) (syn_csn (syn_cuni (syn_cuni (.cv z))))) (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0011 p0018
  have p0020 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))) (syn_csi (syn_csi R)) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z)))))) (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z))))) (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) p0019
  have p0021 :=
    @g_bitrd (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))) (syn_csi (syn_csi R)) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z)))))) (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0008 p0020
  exact p0021

noncomputable def g_wecuttypednclecndv
    (y : Var) (z : Var) (D : Class) (R : Class) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_y_z : y ≠ z) (hyp_wecuttypednclecndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.imp (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ D.fv ∪ R.fv
  have dv_cache_0001 : y ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0006 : Disjoint ((syn_cuni (syn_cuni (.cv y)))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint ((syn_cuni (syn_cuni (.cv y)))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((syn_cuni (.cv y))).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv y)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show y ∉ (R).fv from (by exact dv_R_y))))))))))
  have p0000 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
  have p0001 :=
    @g_simpl (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
  have p0002 :=
    @g_pw12argcl (.cv y) D
  have p0003 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv y))) D) (.classEq (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))))) p0001 p0002
  have p0004 :=
    @g_simpld (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (syn_cuni (.cv y))) D) (.classEq (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y)))))) p0003
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))) (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (syn_cuni (.cv y))) D) p0000 p0004
  have p0006 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
  have p0007 :=
    @g_simpr (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
  have p0008 :=
    @g_pw12argcl (.cv z) D
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv z))) D) (.classEq (.cv z) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z))))))) p0007 p0008
  have p0010 :=
    @g_simpld (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (syn_cuni (.cv z))) D) (.classEq (.cv z) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z)))))) p0009
  have p0011 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))) (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.classMem (syn_cuni (syn_cuni (.cv z))) D) p0006 p0010
  have p0012 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
  have p0013 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
  have p0014 :=
    @g_wecuttypedbrndv y z D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0015 :=
    @g_biimpd (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0014
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))) (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (.imp (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z))))) p0013 p0015
  have p0017 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0012 p0016
  have p0018 :=
    @g_n_3jca (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))) (.classMem (syn_cuni (syn_cuni (.cv y))) D) (.classMem (syn_cuni (syn_cuni (.cv z))) D) (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0005 p0011 p0017
  have p0019 :=
    @g_vex y
  have p0020 :=
    @g_uniex (.cv y) p0019
  have p0021 :=
    @g_uniex (syn_cuni (.cv y)) p0020
  have p0022 :=
    @g_vex z
  have p0023 :=
    @g_uniex (.cv z) p0022
  have p0024 :=
    @g_uniex (syn_cuni (.cv z)) p0023
  have p0025 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni (.cv y))) (syn_cvv)) (.classMem (syn_cuni (syn_cuni (.cv z))) (syn_cvv)) p0021 p0024
  have p0026 :=
    @g_wecutnclecclndv (syn_cuni (syn_cuni (.cv y))) (syn_cuni (syn_cuni (.cv z))) D R dv_cache_0006 hyp_wecuttypednclecndv_1
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))) (syn_w3a (.classMem (syn_cuni (syn_cuni (.cv y))) D) (.classMem (syn_cuni (syn_cuni (.cv z))) D) (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z))))) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z)))))))) p0018 p0027
  have p0029 :=
    @g_ex (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z)))))))) p0028
  exact p0029

noncomputable def g_wecutcardtypedcardleastndv
    (y : Var) (z : Var) (D : Class) (R : Class) (K : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_K_q : q ∉ K.fv) (dv_K_y : y ∉ K.fv) (dv_K_z : z ∉ K.fv) (dv_R_q : q ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_q_y : q ≠ y) (dv_q_z : q ≠ z) (dv_y_z : y ≠ z) (hyp_wecutcardtypedcardleastndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutcardtypedcardleastndv_2 : Nominal.NPrf (.classMem K (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)) (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ D.fv ∪ R.fv ∪ K.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ (K).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_K_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (K).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_K_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (K).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_K_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show q ≠ y from (by exact dv_q_y))
  have dv_cache_0011 : q ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show q ≠ z from (by exact dv_q_z))
  have dv_cache_0012 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0013 : z ∉ ((Wff.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_y_z), dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wecutcardtypedleastndv y z D R K q dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_wecutcardtypedcardleastndv_1 hyp_wecutcardtypedcardleastndv_2
  have p0001 :=
    @g_wecuttypednclecndv y z D R dv_cache_0002 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0012 hyp_wecutcardtypedcardleastndv_1
  have p0002 :=
    @g_imim2d (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z)))))))) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) p0001
  have p0003 :=
    @g_ralimdva (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))))) z (syn_cpw1 (syn_cpw1 D)) dv_cache_0013 p0002
  have p0004 :=
    @g_anim2d (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) p0003
  have p0005 :=
    @g_reximia (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) y (syn_cpw1 (syn_cpw1 D)) p0004
  have p0006 :=
    @g_syl (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)) (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))))) (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))) p0000 p0005
  exact p0006

noncomputable def g_elwppcandstrictslice
    (C : Class) (k : Var) (F : Class) :
    Nominal.NPrf (syn_wb (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C))) := by
  let proofSupport : Finset Var := C.fv ∪ ({k} : Finset Var) ∪ F.fv
  have p0000 :=
    @g_elin (.cv k) (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))
  have p0001 :=
    @g_biid (.classMem (.cv k) (syn_cwppcand F C))
  have p0002 :=
    @g_eliniseg (syn_cltc) C (.cv k)
  have p0003 :=
    @g_anbi12i (.classMem (.cv k) (syn_cwppcand F C)) (.classMem (.cv k) (syn_cwppcand F C)) (.classMem (.cv k) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_wbr (.cv k) (syn_cltc) C) p0001 p0002
  have p0004 :=
    @g_bitri (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.classMem (.cv k) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C)) p0000 p0003
  exact p0004

noncomputable def g_wppreachexndv
    (C : Class) (F : Class) (hyp_wppreachexndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppreach F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach F C)))
  have p0001 :=
    @g_eqid (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0002 :=
    @g_cnvex F hyp_wppreachexndv_1
  have p0003 :=
    @g_imageex (syn_ccnv F) p0002
  have p0004 :=
    @g_frecex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) p0001 p0003
  have p0005 :=
    @g_rnex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0004
  have p0006 :=
    @g_uniex (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) p0005
  have p0007 :=
    @g_eqeltri (syn_cwppreach F C) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) (syn_cvv) p0000 p0006
  exact p0007

noncomputable def g_wppcandexndv
    (C : Class) (F : Class) (hyp_wppcandexndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppcand F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwppcand] using (Nominal.classEqRefl (syn_cwppcand F C)))
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_hwcardsexg (syn_cvv)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_lecex
  have p0005 :=
    @g_cnvex (syn_clec) p0004
  have p0006 :=
    @g_snex C
  have p0007 :=
    @g_imaex (syn_ccnv (syn_clec)) (syn_csn C) p0005 p0006
  have p0008 :=
    @g_inex (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)) p0003 p0007
  have p0009 :=
    @g_wppreachexndv C F hyp_wppcandexndv_1
  have p0010 :=
    @g_inex (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C) p0008 p0009
  have p0011 :=
    @g_eqeltri (syn_cwppcand F C) (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_cwppreach F C)) (syn_cvv) p0000 p0010
  exact p0011

noncomputable def g_wppcandstrictsliceexndv
    (C : Class) (F : Class) (hyp_wppcandstrictsliceexndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_wppcandexndv C F hyp_wppcandstrictsliceexndv_1
  have p0001 :=
    @g_ltcex
  have p0002 :=
    @g_cnvex (syn_cltc) p0001
  have p0003 :=
    @g_snex C
  have p0004 :=
    @g_imaex (syn_ccnv (syn_cltc)) (syn_csn C) p0002 p0003
  have p0005 :=
    @g_inex (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)) p0000 p0004
  exact p0005

noncomputable def g_wppcandnltpivoteqd
    (C : Class) (k : Var) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) (.classEq (.cv k) C)) := by
  let proofSupport : Finset Var := C.fv ∪ ({k} : Finset Var) ∪ F.fv
  have p0000 :=
    @g_id (.classEq (.cv k) C)
  have p0001 :=
    @g_a1i (.imp (.classEq (.cv k) C) (.classEq (.cv k) C)) (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) p0000
  have p0002 :=
    @g_simpl (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))
  have p0003 :=
    @g_elwppcand C (.cv k) F
  have p0004 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C))) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) (.classMem (.cv k) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C))) p0002 p0004
  have p0006 :=
    @g_simpld (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C)) p0005
  have p0007 :=
    @g_simprd (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C) p0006
  have p0008 :=
    @g_brltc (.cv k) C
  have p0009 :=
    @g_biimpri (syn_wbr (.cv k) (syn_cltc) C) (syn_wa (syn_wbr (.cv k) (syn_clec) C) (syn_wne (.cv k) C)) p0008
  have p0010 :=
    @g_ex (syn_wbr (.cv k) (syn_clec) C) (syn_wne (.cv k) C) (syn_wbr (.cv k) (syn_cltc) C) p0009
  have p0011 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) (syn_wbr (.cv k) (syn_clec) C) (.imp (syn_wne (.cv k) C) (syn_wbr (.cv k) (syn_cltc) C)) p0007 p0010
  have p0012 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))
  have p0013 :=
    @g_pm2_21d (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) (syn_wbr (.cv k) (syn_cltc) C) (.classEq (.cv k) C) p0012
  have p0014 :=
    @g_syld (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) (syn_wne (.cv k) C) (syn_wbr (.cv k) (syn_cltc) C) (.classEq (.cv k) C) p0011 p0013
  have p0015 :=
    @g_pm2_61dne (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) (.classEq (.cv k) C) (.cv k) C p0001 p0014
  exact p0015

#print axioms g_wppcandnltpivoteqd

end NFChoice.DirectNominalPrf.WPPReplay
