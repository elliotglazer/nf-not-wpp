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
import NominalWPPReplayChunk013Compact001Part050

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

noncomputable def g_lectr
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.imp (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) C)) (syn_wbr A (syn_clec) C))) := by
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
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.classEq B (syn_cplc A (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classEq C (syn_cplc B (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_B, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0010 : x ∉ ((syn_wbr A (syn_clec) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_wbr A (syn_clec) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dflec2 A B x dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_n_3adant3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (syn_wb (syn_wbr A (syn_clec) B) (syn_wrex x (syn_cncs) (.classEq B (syn_cplc A (.cv x))))) (.classMem C (syn_cncs)) p0000
  have p0002 :=
    @g_dflec2 B C y dv_cache_0003 dv_cache_0004
  have p0003 :=
    @g_n_3adant1 (.classMem B (syn_cncs)) (.classMem C (syn_cncs)) (syn_wb (syn_wbr B (syn_clec) C) (syn_wrex y (syn_cncs) (.classEq C (syn_cplc B (.cv y))))) (.classMem A (syn_cncs)) p0002
  have p0004 :=
    @g_anbi12d (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wbr A (syn_clec) B) (syn_wrex x (syn_cncs) (.classEq B (syn_cplc A (.cv x)))) (syn_wbr B (syn_clec) C) (syn_wrex y (syn_cncs) (.classEq C (syn_cplc B (.cv y)))) p0001 p0003
  have p0005 :=
    @g_reeanv (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y))) x y (syn_cncs) (syn_cncs) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0006 :=
    @g_syl6bbr (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) C)) (syn_wa (syn_wrex x (syn_cncs) (.classEq B (syn_cplc A (.cv x)))) (syn_wrex y (syn_cncs) (.classEq C (syn_cplc B (.cv y))))) (syn_wrex x (syn_cncs) (syn_wrex y (syn_cncs) (syn_wa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y)))))) p0004 p0005
  have p0007 :=
    @g_addceq1 B (syn_cplc A (.cv x)) (.cv y)
  have p0008 :=
    @g_addcass A (.cv x) (.cv y)
  have p0009 :=
    @g_syl6eq (.classEq B (syn_cplc A (.cv x))) (syn_cplc B (.cv y)) (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_cplc A (syn_cplc (.cv x) (.cv y))) p0007 p0008
  have p0010 :=
    @g_eqeq2d (.classEq B (syn_cplc A (.cv x))) (syn_cplc B (.cv y)) (syn_cplc A (syn_cplc (.cv x) (.cv y))) C p0009
  have p0011 :=
    @g_biimpa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y))) (.classEq C (syn_cplc A (syn_cplc (.cv x) (.cv y)))) p0010
  have p0012 :=
    @g_simp1 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
  have p0013 :=
    @g_ncaddccl (.cv x) (.cv y)
  have p0014 :=
    @g_addlecncs A (syn_cplc (.cv x) (.cv y))
  have p0015 :=
    @g_syl2an (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.classMem A (syn_cncs)) (.classMem (syn_cplc (.cv x) (.cv y)) (syn_cncs)) (syn_wbr A (syn_clec) (syn_cplc A (syn_cplc (.cv x) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv y) (syn_cncs))) p0012 p0013 p0014
  have p0016 :=
    @g_breq2 C (syn_cplc A (syn_cplc (.cv x) (.cv y))) A (syn_clec)
  have p0017 :=
    @g_syl5ibrcom (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv y) (syn_cncs)))) (syn_wbr A (syn_clec) C) (.classEq C (syn_cplc A (syn_cplc (.cv x) (.cv y)))) (syn_wbr A (syn_clec) (syn_cplc A (syn_cplc (.cv x) (.cv y)))) p0015 p0016
  have p0018 :=
    @g_syl5 (syn_wa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y)))) (.classEq C (syn_cplc A (syn_cplc (.cv x) (.cv y)))) (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv y) (syn_cncs)))) (syn_wbr A (syn_clec) C) p0011 p0017
  have p0019 :=
    @g_rexlimdvva (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y)))) (syn_wbr A (syn_clec) C) x y (syn_cncs) (syn_cncs) dv_cache_0005 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0009 p0018
  have p0020 :=
    @g_sylbid (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wa (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) C)) (syn_wrex x (syn_cncs) (syn_wrex y (syn_cncs) (syn_wa (.classEq B (syn_cplc A (.cv x))) (.classEq C (syn_cplc B (.cv y)))))) (syn_wbr A (syn_clec) C) p0006 p0019
  exact p0020

noncomputable def g_nc0le1
    (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cncs)) (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N))) := by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (h)
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (h)
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (h)
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_q : a ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_q_ne_a : q ≠ a :=
    Ne.symm fresh_a_ne_q
  have fresh_a_ne_p : a ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_q_ne_p : q ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have dv_cache_0001 : a ∉ (N).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_cnc (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_wss (.cv q) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ ((syn_wss (syn_csn (.cv x)) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0011 : x ∉ ((syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_q, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((syn_cnc (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : q ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show q ≠ p from (by exact fresh_q_ne_p))
  have dv_cache_0015 : a ∉ ((syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs a N dv_cache_0001
  have p0001 :=
    @g_nceq (.cv a) (syn_c0)
  have p0002 :=
    @g_df0c2
  have p0003 :=
    @g_syl6eqr (.classEq (.cv a) (syn_c0)) (syn_cnc (.cv a)) (syn_cnc (syn_c0)) (syn_c0c) p0001 p0002
  have p0004 :=
    @g_orcd (.classEq (.cv a) (syn_c0)) (.classEq (syn_cnc (.cv a)) (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))) p0003
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_snss (.cv x) (.cv a) p0005
  have p0007 :=
    @g_vex a
  have p0008 :=
    @g_ncid (.cv a) p0007
  have p0009 :=
    @g_snel1c (.cv x) p0005
  have p0010 :=
    @g_sseq2 (.cv p) (.cv a) (.cv q)
  have p0011 :=
    @g_sseq1 (.cv q) (syn_csn (.cv x)) (.cv a)
  have p0012 :=
    @g_rspc2ev (syn_wss (.cv q) (.cv p)) (syn_wss (syn_csn (.cv x)) (.cv a)) (syn_wss (.cv q) (.cv a)) p q (.cv a) (syn_csn (.cv x)) (syn_cnc (.cv a)) (syn_c1c) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0010 p0011
  have p0013 :=
    @g_mp3an12 (.classMem (.cv a) (syn_cnc (.cv a))) (.classMem (syn_csn (.cv x)) (syn_c1c)) (syn_wss (syn_csn (.cv x)) (.cv a)) (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p)))) p0008 p0009 p0012
  have p0014_e00_recanon : Nominal.NPrf (syn_wb (.objMem x a) (syn_wss (syn_csn (.cv x)) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0006
  have p0014 :=
    @g_sylbi (.objMem x a) (syn_wss (syn_csn (.cv x)) (.cv a)) (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p)))) p0014_e00_recanon p0013
  have p0015 :=
    @g_exlimiv (.objMem x a) (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p)))) x dv_cache_0011 p0014
  have p0016 :=
    @g_n0 x (.cv a) dv_cache_0012
  have p0017 :=
    @g_n_1cex
  have p0018 :=
    @g_ncex (.cv a)
  have p0019 :=
    @g_brlec q p (syn_c1c) (syn_cnc (.cv a)) dv_cache_0007 dv_cache_0013 dv_cache_0005 dv_cache_0014 p0017 p0018
  have p0020 :=
    @g_rexcom (syn_wss (.cv q) (.cv p)) q p (syn_c1c) (syn_cnc (.cv a)) dv_cache_0006 dv_cache_0013 dv_cache_0014
  have p0021 :=
    @g_bitri (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))) (syn_wrex q (syn_c1c) (syn_wrex p (syn_cnc (.cv a)) (syn_wss (.cv q) (.cv p)))) (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p)))) p0019 p0020
  have p0022_e01_recanon : Nominal.NPrf (syn_wb (syn_wne (.cv a) (syn_c0)) (syn_wex x (.objMem x a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0022 :=
    @g_n_3imtr4i (syn_wex x (.objMem x a)) (syn_wrex p (syn_cnc (.cv a)) (syn_wrex q (syn_c1c) (syn_wss (.cv q) (.cv p)))) (syn_wne (.cv a) (syn_c0)) (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))) p0015 p0022_e01_recanon p0021
  have p0023 :=
    @g_olcd (syn_wne (.cv a) (syn_c0)) (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))) (.classEq (syn_cnc (.cv a)) (syn_c0c)) p0022
  have p0024 :=
    @g_pm2_61ine (syn_wo (.classEq (syn_cnc (.cv a)) (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a)))) (.cv a) (syn_c0) p0004 p0023
  have p0025 :=
    @g_eqeq1 N (syn_cnc (.cv a)) (syn_c0c)
  have p0026 :=
    @g_breq2 N (syn_cnc (.cv a)) (syn_c1c) (syn_clec)
  have p0027 :=
    @g_orbi12d (.classEq N (syn_cnc (.cv a))) (.classEq N (syn_c0c)) (.classEq (syn_cnc (.cv a)) (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N) (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a))) p0025 p0026
  have p0028 :=
    @g_mpbiri (.classEq N (syn_cnc (.cv a))) (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N)) (syn_wo (.classEq (syn_cnc (.cv a)) (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) (syn_cnc (.cv a)))) p0024 p0027
  have p0029 :=
    @g_exlimiv (.classEq N (syn_cnc (.cv a))) (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N)) a dv_cache_0015 p0028
  have p0030 :=
    @g_sylbi (.classMem N (syn_cncs)) (syn_wex a (.classEq N (syn_cnc (.cv a)))) (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N)) p0000 p0029
  exact p0030

noncomputable def g_nc0suc
    (m : Var) (N : Class) (dv_N_m : m ∉ N.fv) :
    Nominal.NPrf (.imp (.classMem N (syn_cncs)) (syn_wo (.classEq N (syn_c0c)) (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c)))))) := by
  let proofSupport : Finset Var := ({m} : Finset Var) ∪ N.fv
  have dv_cache_0001 : m ∉ ((syn_c1c)).fv := by
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : m ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nc0le1 N
  have p0001 :=
    @g_n_1cnc
  have p0002 :=
    @g_dflec2 (syn_c1c) N m dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_addccom (syn_c1c) (.cv m)
  have p0004 :=
    @g_eqeq2i (syn_cplc (syn_c1c) (.cv m)) (syn_cplc (.cv m) (syn_c1c)) N p0003
  have p0005 :=
    @g_rexbii (.classEq N (syn_cplc (syn_c1c) (.cv m))) (.classEq N (syn_cplc (.cv m) (syn_c1c))) m (syn_cncs) p0004
  have p0006 :=
    @g_syl6bb (syn_wa (.classMem (syn_c1c) (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr (syn_c1c) (syn_clec) N) (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (syn_c1c) (.cv m)))) (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c)))) p0002 p0005
  have p0007 :=
    @g_mpan (.classMem (syn_c1c) (syn_cncs)) (.classMem N (syn_cncs)) (syn_wb (syn_wbr (syn_c1c) (syn_clec) N) (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c))))) p0001 p0006
  have p0008 :=
    @g_orbi2d (.classMem N (syn_cncs)) (syn_wbr (syn_c1c) (syn_clec) N) (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c)))) (.classEq N (syn_c0c)) p0007
  have p0009 :=
    @g_mpbid (.classMem N (syn_cncs)) (syn_wo (.classEq N (syn_c0c)) (syn_wbr (syn_c1c) (syn_clec) N)) (syn_wo (.classEq N (syn_c0c)) (syn_wrex m (syn_cncs) (.classEq N (syn_cplc (.cv m) (syn_c1c))))) p0000 p0008
  exact p0009

noncomputable def g_addceq0
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wb (.classEq (syn_cplc A B) (syn_c0c)) (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Wff.neg (.classEq (syn_cplc A B) (syn_c0c)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ianor (.classEq A (syn_c0c)) (.classEq B (syn_c0c))
  have p0001 :=
    @g_nc0suc p A dv_cache_0001
  have p0002 :=
    @g_ord (.classMem A (syn_cncs)) (.classEq A (syn_c0c)) (syn_wrex p (syn_cncs) (.classEq A (syn_cplc (.cv p) (syn_c1c)))) p0001
  have p0003 :=
    @g_adantr (.classMem A (syn_cncs)) (.imp (.neg (.classEq A (syn_c0c))) (syn_wrex p (syn_cncs) (.classEq A (syn_cplc (.cv p) (syn_c1c))))) (.classMem B (syn_cncs)) p0002
  have p0004 :=
    @g_addc32 (.cv p) (syn_c1c) B
  have p0005 :=
    @g_n_0cnsuc (syn_cplc (.cv p) B)
  have p0006 :=
    @g_eqnetri (syn_cplc (syn_cplc (.cv p) (syn_c1c)) B) (syn_cplc (syn_cplc (.cv p) B) (syn_c1c)) (syn_c0c) p0004 p0005
  have p0007 :=
    @g_addceq1 A (syn_cplc (.cv p) (syn_c1c)) B
  have p0008 :=
    @g_eqeq1d (.classEq A (syn_cplc (.cv p) (syn_c1c))) (syn_cplc A B) (syn_cplc (syn_cplc (.cv p) (syn_c1c)) B) (syn_c0c) p0007
  have p0009 :=
    @g_necon3bbid (.classEq A (syn_cplc (.cv p) (syn_c1c))) (.classEq (syn_cplc A B) (syn_c0c)) (syn_cplc (syn_cplc (.cv p) (syn_c1c)) B) (syn_c0c) p0008
  have p0010 :=
    @g_mpbiri (.classEq A (syn_cplc (.cv p) (syn_c1c))) (.neg (.classEq (syn_cplc A B) (syn_c0c))) (syn_wne (syn_cplc (syn_cplc (.cv p) (syn_c1c)) B) (syn_c0c)) p0006 p0009
  have p0011 :=
    @g_rexlimivw (.classEq A (syn_cplc (.cv p) (syn_c1c))) (.neg (.classEq (syn_cplc A B) (syn_c0c))) p (syn_cncs) dv_cache_0002 p0010
  have p0012 :=
    @g_syl6 (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.neg (.classEq A (syn_c0c))) (syn_wrex p (syn_cncs) (.classEq A (syn_cplc (.cv p) (syn_c1c)))) (.neg (.classEq (syn_cplc A B) (syn_c0c))) p0003 p0011
  have p0013 :=
    @g_nc0suc p B dv_cache_0003
  have p0014 :=
    @g_ord (.classMem B (syn_cncs)) (.classEq B (syn_c0c)) (syn_wrex p (syn_cncs) (.classEq B (syn_cplc (.cv p) (syn_c1c)))) p0013
  have p0015 :=
    @g_adantl (.classMem B (syn_cncs)) (.imp (.neg (.classEq B (syn_c0c))) (syn_wrex p (syn_cncs) (.classEq B (syn_cplc (.cv p) (syn_c1c))))) (.classMem A (syn_cncs)) p0014
  have p0016 :=
    @g_addcass A (.cv p) (syn_c1c)
  have p0017 :=
    @g_n_0cnsuc (syn_cplc A (.cv p))
  have p0018 :=
    @g_eqnetrri (syn_cplc (syn_cplc A (.cv p)) (syn_c1c)) (syn_cplc A (syn_cplc (.cv p) (syn_c1c))) (syn_c0c) p0016 p0017
  have p0019 :=
    @g_addceq2 B (syn_cplc (.cv p) (syn_c1c)) A
  have p0020 :=
    @g_eqeq1d (.classEq B (syn_cplc (.cv p) (syn_c1c))) (syn_cplc A B) (syn_cplc A (syn_cplc (.cv p) (syn_c1c))) (syn_c0c) p0019
  have p0021 :=
    @g_necon3bbid (.classEq B (syn_cplc (.cv p) (syn_c1c))) (.classEq (syn_cplc A B) (syn_c0c)) (syn_cplc A (syn_cplc (.cv p) (syn_c1c))) (syn_c0c) p0020
  have p0022 :=
    @g_mpbiri (.classEq B (syn_cplc (.cv p) (syn_c1c))) (.neg (.classEq (syn_cplc A B) (syn_c0c))) (syn_wne (syn_cplc A (syn_cplc (.cv p) (syn_c1c))) (syn_c0c)) p0018 p0021
  have p0023 :=
    @g_rexlimivw (.classEq B (syn_cplc (.cv p) (syn_c1c))) (.neg (.classEq (syn_cplc A B) (syn_c0c))) p (syn_cncs) dv_cache_0002 p0022
  have p0024 :=
    @g_syl6 (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.neg (.classEq B (syn_c0c))) (syn_wrex p (syn_cncs) (.classEq B (syn_cplc (.cv p) (syn_c1c)))) (.neg (.classEq (syn_cplc A B) (syn_c0c))) p0015 p0023
  have p0025 :=
    @g_jaod (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.neg (.classEq A (syn_c0c))) (.neg (.classEq (syn_cplc A B) (syn_c0c))) (.neg (.classEq B (syn_c0c))) p0012 p0024
  have p0026 :=
    @g_syl5bi (.neg (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c)))) (syn_wo (.neg (.classEq A (syn_c0c))) (.neg (.classEq B (syn_c0c)))) (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.neg (.classEq (syn_cplc A B) (syn_c0c))) p0000 p0025
  have p0027 :=
    @g_con4d (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c))) (.classEq (syn_cplc A B) (syn_c0c)) p0026
  have p0028 :=
    @g_addceq12 A B (syn_c0c) (syn_c0c)
  have p0029 :=
    @g_addcid2 (syn_c0c)
  have p0030 :=
    @g_syl6eq (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c))) (syn_cplc A B) (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c) p0028 p0029
  have p0031 :=
    @g_impbid1 (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.classEq (syn_cplc A B) (syn_c0c)) (syn_wa (.classEq A (syn_c0c)) (.classEq B (syn_c0c))) p0027 p0030
  exact p0031

#print axioms g_addceq0

end NFChoice.DirectNominalPrf.WPPReplay
