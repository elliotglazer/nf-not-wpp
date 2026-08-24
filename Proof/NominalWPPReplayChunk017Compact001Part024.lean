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
import NominalWPPReplayChunk017Compact001Part023

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

noncomputable def g_hncodecmpsetstrictcutsemclndv
    (x : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v_ne_u : v ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have dv_cache_0001 : x ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cfv (syn_c2nd) C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv v) C)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv u) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0009 : v ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0010 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((Wff.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_v, fresh_u_not_A, fresh_u_not_B, fresh_u_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : v ∉ ((Wff.imp (.classMem B (syn_cvv)) (.imp (.classMem C (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_C, fresh_v_not_A, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0001 :=
    @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0002 :=
    @g_elex B (syn_chwcn A)
  have p0003 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0005 :=
    @g_elex C (syn_chwcn A)
  have p0006 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_id (.classEq (.cv v) C)
  have p0008 :=
    @g_eleq1d (.classEq (.cv v) C) (.cv v) C (syn_chwcn A) p0007
  have p0009 :=
    @g_eqid B
  have p0010 :=
    @g_a1i (.classEq B B) (.classEq (.cv v) C) p0009
  have p0011 :=
    @g_id (.classEq (.cv v) C)
  have p0012 :=
    @g_breq12d (.classEq (.cv v) C) B B (.cv v) C (syn_chncodecmpset A) p0010 p0011
  have p0013 :=
    @g_eqid B
  have p0014 :=
    @g_a1i (.classEq B B) (.classEq (.cv v) C) p0013
  have p0015 :=
    @g_id (.classEq (.cv v) C)
  have p0016 :=
    @g_breq12d (.classEq (.cv v) C) B B (.cv v) C (syn_chwniso A) p0014 p0015
  have p0017 :=
    @g_id (.classEq (.cv v) C)
  have p0018 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c2nd) p0017
  have p0019 :=
    @g_eqid B
  have p0020 :=
    @g_a1i (.classEq B B) (.classEq (.cv v) C) p0019
  have p0021 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0022 :=
    @g_a1i (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (.classEq (.cv v) C) p0021
  have p0023 :=
    @g_id (.classEq (.cv v) C)
  have p0024 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c1st) p0023
  have p0025 :=
    @g_id (.classEq (.cv v) C)
  have p0026 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c2nd) p0025
  have p0027 :=
    @g_id (.classEq (.cv v) C)
  have p0028 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c1st) p0027
  have p0029 :=
    @g_difeq1d (.classEq (.cv v) C) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (syn_cid) p0028
  have p0030 :=
    @g_cnveqd (.classEq (.cv v) C) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)) p0029
  have p0031 :=
    @g_imaeq1d (.classEq (.cv v) C) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)) p0030
  have p0032 :=
    @g_ineq12d (.classEq (.cv v) C) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))) p0026 p0031
  have p0033 :=
    @g_id (.classEq (.cv v) C)
  have p0034 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c2nd) p0033
  have p0035 :=
    @g_id (.classEq (.cv v) C)
  have p0036 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c1st) p0035
  have p0037 :=
    @g_difeq1d (.classEq (.cv v) C) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (syn_cid) p0036
  have p0038 :=
    @g_cnveqd (.classEq (.cv v) C) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)) p0037
  have p0039 :=
    @g_imaeq1d (.classEq (.cv v) C) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)) p0038
  have p0040 :=
    @g_ineq12d (.classEq (.cv v) C) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))) p0034 p0039
  have p0041 :=
    @g_xpeq12d (.classEq (.cv v) C) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))) p0032 p0040
  have p0042 :=
    @g_ineq12d (.classEq (.cv v) C) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))))) p0024 p0041
  have p0043 :=
    @g_id (.classEq (.cv v) C)
  have p0044 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c2nd) p0043
  have p0045 :=
    @g_id (.classEq (.cv v) C)
  have p0046 :=
    @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c1st) p0045
  have p0047 :=
    @g_difeq1d (.classEq (.cv v) C) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (syn_cid) p0046
  have p0048 :=
    @g_cnveqd (.classEq (.cv v) C) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)) p0047
  have p0049 :=
    @g_imaeq1d (.classEq (.cv v) C) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)) p0048
  have p0050 :=
    @g_ineq12d (.classEq (.cv v) C) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))) p0044 p0049
  have p0051 :=
    @g_opeq12d (.classEq (.cv v) C) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) C) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))) p0042 p0050
  have p0052 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))
  have p0053 :=
    @g_a1i (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) C) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))))) (.classEq (.cv v) C) p0052
  have p0054 :=
    @g_eqcomd (.classEq (.cv v) C) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) C) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))))) p0053
  have p0055 :=
    @g_n_3eqtrd (.classEq (.cv v) C) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))))) (syn_cop (syn_cin (syn_cfv (syn_c1st) C) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) C) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))))) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)) p0022 p0051 p0054
  have p0056 :=
    @g_breq12d (.classEq (.cv v) C) B B (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)) (syn_chwniso A) p0020 p0055
  have p0057 :=
    @g_rexeqbidv (.classEq (.cv v) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))) x (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0018 p0056
  have p0058 :=
    @g_orbi12d (.classEq (.cv v) C) (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))) p0016 p0057
  have p0059 :=
    @g_bibi12d (.classEq (.cv v) C) (syn_wbr B (syn_chncodecmpset A) (.cv v)) (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))) p0012 p0058
  have p0060 :=
    @g_imbi12d (.classEq (.cv v) C) (.classMem (.cv v) (syn_chwcn A)) (.classMem C (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))))) p0008 p0059
  have p0061 :=
    @g_imbi2d (.classEq (.cv v) C) (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))))) (.imp (.classMem C (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))))) (.classMem B (syn_cvv)) p0060
  have p0062 :=
    @g_eqid (.cv v)
  have p0063 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0062
  have p0064 :=
    @g_eleq1d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_chwcn A) p0063
  have p0065 :=
    @g_id (.classEq (.cv u) B)
  have p0066 :=
    @g_eqid (.cv v)
  have p0067 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0066
  have p0068 :=
    @g_breq12d (.classEq (.cv u) B) (.cv u) B (.cv v) (.cv v) (syn_chncodecmpset A) p0065 p0067
  have p0069 :=
    @g_id (.classEq (.cv u) B)
  have p0070 :=
    @g_eqid (.cv v)
  have p0071 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0070
  have p0072 :=
    @g_breq12d (.classEq (.cv u) B) (.cv u) B (.cv v) (.cv v) (syn_chwniso A) p0069 p0071
  have p0073 :=
    @g_eqid (.cv v)
  have p0074 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0073
  have p0075 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c2nd) p0074
  have p0076 :=
    @g_id (.classEq (.cv u) B)
  have p0077 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0078 :=
    @g_a1i (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (.classEq (.cv u) B) p0077
  have p0079 :=
    @g_eqid (.cv v)
  have p0080 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0079
  have p0081 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c1st) p0080
  have p0082 :=
    @g_eqid (.cv v)
  have p0083 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0082
  have p0084 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c2nd) p0083
  have p0085 :=
    @g_eqid (.cv v)
  have p0086 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0085
  have p0087 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c1st) p0086
  have p0088 :=
    @g_difeq1d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv v)) (syn_cid) p0087
  have p0089 :=
    @g_cnveqd (.classEq (.cv u) B) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) p0088
  have p0090 :=
    @g_imaeq1d (.classEq (.cv u) B) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)) p0089
  have p0091 :=
    @g_ineq12d (.classEq (.cv u) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))) p0084 p0090
  have p0092 :=
    @g_eqid (.cv v)
  have p0093 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0092
  have p0094 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c2nd) p0093
  have p0095 :=
    @g_eqid (.cv v)
  have p0096 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0095
  have p0097 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c1st) p0096
  have p0098 :=
    @g_difeq1d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv v)) (syn_cid) p0097
  have p0099 :=
    @g_cnveqd (.classEq (.cv u) B) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) p0098
  have p0100 :=
    @g_imaeq1d (.classEq (.cv u) B) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)) p0099
  have p0101 :=
    @g_ineq12d (.classEq (.cv u) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))) p0094 p0100
  have p0102 :=
    @g_xpeq12d (.classEq (.cv u) B) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) p0091 p0101
  have p0103 :=
    @g_ineq12d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))))) p0081 p0102
  have p0104 :=
    @g_eqid (.cv v)
  have p0105 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0104
  have p0106 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c2nd) p0105
  have p0107 :=
    @g_eqid (.cv v)
  have p0108 :=
    @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0107
  have p0109 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c1st) p0108
  have p0110 :=
    @g_difeq1d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv v)) (syn_cid) p0109
  have p0111 :=
    @g_cnveqd (.classEq (.cv u) B) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) p0110
  have p0112 :=
    @g_imaeq1d (.classEq (.cv u) B) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)) p0111
  have p0113 :=
    @g_ineq12d (.classEq (.cv u) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))) p0106 p0112
  have p0114 :=
    @g_opeq12d (.classEq (.cv u) B) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) p0103 p0113
  have p0115 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
  have p0116 :=
    @g_a1i (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (.classEq (.cv u) B) p0115
  have p0117 :=
    @g_eqcomd (.classEq (.cv u) B) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))))) p0116
  have p0118 :=
    @g_n_3eqtrd (.classEq (.cv u) B) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))))) (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v)) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x))))) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) p0078 p0114 p0117
  have p0119 :=
    @g_breq12d (.classEq (.cv u) B) (.cv u) B (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)) (syn_chwniso A) p0076 p0118
  have p0120 :=
    @g_rexeqbidv (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))) x (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0001 dv_cache_0001 dv_cache_0004 p0075 p0119
  have p0121 :=
    @g_orbi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) p0072 p0120
  have p0122 :=
    @g_bibi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr B (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))) p0068 p0121
  have p0123 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))) p0064 p0122
  have p0124 :=
    @g_hncodecmpsetstrictcutsemdv x v u A dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0125 :=
    @g_vtoclg (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))))) (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))))) u B (syn_cvv) dv_cache_0010 dv_cache_0011 p0123 p0124
  have p0126 :=
    @g_vtoclg (.imp (.classMem B (syn_cvv)) (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))))) (.imp (.classMem B (syn_cvv)) (.imp (.classMem C (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))))))) v C (syn_cvv) dv_cache_0012 dv_cache_0013 p0061 p0125
  have p0127 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem C (syn_cvv)) (.imp (.classMem B (syn_cvv)) (.imp (.classMem C (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))))))) p0006 p0126
  have p0128 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_cvv)) (.imp (.classMem C (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))))) p0003 p0127
  have p0129 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem C (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))))) p0000 p0128
  exact p0129

noncomputable def g_hncodetotalleftmemndv
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_chwcn A)) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_hncodecmpdefaultcnndv A
  have p0001 :=
    @g_simpr (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))
  have p0002 :=
    @g_simpl (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.neg (.classMem (.cv u) (syn_chwcn A)))
  have p0003 :=
    @g_ifclda (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A) p0001 p0002
  have p0004 :=
    Nominal.mp p0000 p0003
  exact p0004

noncomputable def g_hncodetotalrightmemndv
    (v : Var) (A : Class) (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_chwcn A)) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_hncodecmpdefaultcnndv A
  have p0001 :=
    @g_simpr (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0002 :=
    @g_simpl (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.neg (.classMem (.cv v) (syn_chwcn A)))
  have p0003 :=
    @g_ifclda (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A) p0001 p0002
  have p0004 :=
    Nominal.mp p0000 p0003
  exact p0004

noncomputable def g_hncodecomparisontotalndv
    (x : Var) (v : Var) (u : Var) (A : Class) (h : Var) (dv_A_h : h ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_h_x : h ≠ x) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf (syn_w3o (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({h} : Finset Var)
  have dv_cache_0001 : h ∉ ((syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_h_u, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ ((syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_h_v, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_v_x), dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : h ∉ ((syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_h_u, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : h ∉ ((syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_h_v, dv_A_h, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_v_x), dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : h ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ x from (by exact dv_h_x))
  have p0000 :=
    @g_hncodecmpdefaultcnndv A
  have p0001 :=
    @g_simpr (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))
  have p0002 :=
    @g_simpl (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.neg (.classMem (.cv u) (syn_chwcn A)))
  have p0003 :=
    @g_ifclda (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A) p0001 p0002
  have p0004 :=
    Nominal.mp p0000 p0003
  have p0005 :=
    @g_hwcnweclndv A (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_hncodecmpdefaultcnndv A
  have p0008 :=
    @g_simpr (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0009 :=
    @g_simpl (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.neg (.classMem (.cv v) (syn_chwcn A)))
  have p0010 :=
    @g_ifclda (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A) p0008 p0009
  have p0011 :=
    Nominal.mp p0007 p0010
  have p0012 :=
    @g_hwcnweclndv A (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_wecomparisonterminalfdv x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) h (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0006 p0013
  exact p0014

#print axioms g_hncodecomparisontotalndv

end NFChoice.DirectNominalPrf.WPPReplay
