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
import NominalWPPReplayChunk014Compact001Part050

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

noncomputable def g_hnwcutclassordcl
    (B : Class) (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutclassordcl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem B D) (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D))) := by
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
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.imp (.classMem B D) (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex B D
  have p0001 :=
    @g_eleq1 (.cv x) B D
  have p0002 :=
    @g_hnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0003 :=
    @g_eceq1 (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B) (syn_chwniso D)
  have p0004 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))) p0002 p0003
  have p0005 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D) p0004
  have p0006 :=
    @g_imbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D) (.classMem (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_chnord D)) (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D)) p0001 p0005
  have p0007 :=
    @g_hnwcutclassord x D R dv_cache_0002 hyp_hnwcutclassordcl_1
  have p0008 :=
    @g_vtoclg (.imp (.classMem (.cv x) D) (.classMem (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_chnord D))) (.imp (.classMem B D) (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D))) x B (syn_cvv) dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B D) (.classMem (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_chnord D)) p0000 p0008
  exact p0009

noncomputable def g_hnwcutmapf
    (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutmapf_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0004 : p ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_chnord D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_hnwcutmap D R p dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_pw12argcl (.cv p) D
  have p0002 :=
    @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv p))) D) (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))) p0001
  have p0003 :=
    @g_hnwcutclassordcl (syn_cuni (syn_cuni (.cv p))) D R dv_cache_0003 hyp_hnwcutmapf_1
  have p0004 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv p))) D) (.classMem (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D)) (syn_chnord D)) p0002 p0003
  have p0005 :=
    @g_fmpti p (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D)) (syn_chnwcutmap R D) dv_cache_0004 dv_cache_0005 p0000 p0004
  exact p0005

noncomputable def g_hnwcutmapval
    (D : Class) (R : Class) (q : Var) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutmapval_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({q} : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_q : p ≠ q := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : Disjoint ((syn_cuni (syn_cuni (.cv p)))).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint ((syn_cuni (syn_cuni (.cv p)))).fv (R).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((syn_cuni (.cv p))).fv) ((R).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show Disjoint (((Class.cv p)).fv) ((R).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact fresh_p_not_R))))))))))
  have dv_cache_0004 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0005 : p ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, fresh_p_not_D, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_hnwcutmap D R p dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_a1i (.classEq (syn_chnwcutmap R D) (syn_cmpt p (syn_cpw1 (syn_cpw1 D)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0000
  have p0002 :=
    @g_unieq (.cv p) (.cv q)
  have p0003 :=
    @g_unieqd (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) p0002
  have p0004 :=
    @g_hnwcutcodeeq3 (syn_cuni (syn_cuni (.cv p))) (syn_cuni (syn_cuni (.cv q))) D R dv_cache_0003
  have p0005 :=
    @g_syl (.classEq (.cv p) (.cv q)) (.classEq (syn_cuni (syn_cuni (.cv p))) (syn_cuni (syn_cuni (.cv q)))) (.classEq (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0003 p0004
  have p0006 :=
    @g_eceq1 (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)
  have p0007 :=
    @g_syl (.classEq (.cv p) (.cv q)) (.classEq (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))) p0005 p0006
  have p0008 :=
    @g_adantl (.classEq (.cv p) (.cv q)) (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0007
  have p0009 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0010 :=
    @g_pw12argcl (.cv q) D
  have p0011 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0010
  have p0012 :=
    @g_hnwcutclassordcl (syn_cuni (syn_cuni (.cv q))) D R dv_cache_0004 hyp_hnwcutmapval_1
  have p0013 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_chnord D)) p0011 p0012
  have p0014 :=
    @g_elex (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_chnord D)
  have p0015 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_chnord D)) (.classMem (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_fvmptd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p (.cv q) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_cpw1 (syn_cpw1 D)) (syn_chnwcutmap R D) (syn_cvv) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0001 p0008 p0009 p0015
  exact p0016

noncomputable def g_hnwcutcodeltnoiso
    (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_strictseghwnisono x y D R
  have p0001 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x))))
  have p0002 :=
    @g_breq1 (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (.cv y))))
  have p0005 :=
    @g_breq2 (syn_chnwcutcode R D (.cv y)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_bitri (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0003 p0006
  have p0008 :=
    @g_biimpi (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0007
  have p0009 :=
    @g_a1i (.imp (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0008
  have p0010 :=
    @g_mtod (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))) (syn_wbr (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chwniso D) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) p0000 p0009
  exact p0010

noncomputable def g_hwnisoclasseqbcl
    (A : Class) (B : Class) (C : Class) (hyp_hwnisoclasseqbcl_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chwniso A) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have dv_cache_0001 : u ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((Wff.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chwniso A) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_A, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ ((Wff.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr B (syn_chwniso A) (.cv v))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A, fresh_u_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0001 :=
    @g_elex B (syn_chwcn A)
  have p0002 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0004 :=
    @g_elex C (syn_chwcn A)
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_eleq1 (.cv u) B (syn_chwcn A)
  have p0008 :=
    @g_biid (.classMem (.cv v) (syn_chwcn A))
  have p0009 :=
    @g_a1i (syn_wb (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classEq (.cv u) B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0007 p0009
  have p0011 :=
    @g_eceq1 (.cv u) B (syn_chwniso A)
  have p0012 :=
    @g_eqeq1d (.classEq (.cv u) B) (syn_cec (.cv u) (syn_chwniso A)) (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)) p0011
  have p0013 :=
    @g_breq1 (.cv u) B (.cv v) (syn_chwniso A)
  have p0014 :=
    @g_bibi12d (.classEq (.cv u) B) (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) (.cv v)) p0012 p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv u) B) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr B (syn_chwniso A) (.cv v))) p0010 p0014
  have p0016 :=
    @g_biid (.classMem B (syn_chwcn A))
  have p0017 :=
    @g_a1i (syn_wb (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A))) (.classEq (.cv v) C) p0016
  have p0018 :=
    @g_eleq1 (.cv v) C (syn_chwcn A)
  have p0019 :=
    @g_anbi12d (.classEq (.cv v) C) (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem C (syn_chwcn A)) p0017 p0018
  have p0020 :=
    @g_eceq1 (.cv v) C (syn_chwniso A)
  have p0021 :=
    @g_eqeq2d (.classEq (.cv v) C) (syn_cec (.cv v) (syn_chwniso A)) (syn_cec C (syn_chwniso A)) (syn_cec B (syn_chwniso A)) p0020
  have p0022 :=
    @g_breq2 (.cv v) C B (syn_chwniso A)
  have p0023 :=
    @g_bibi12d (.classEq (.cv v) C) (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwniso A) C) p0021 p0022
  have p0024 :=
    @g_imbi12d (.classEq (.cv v) C) (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr B (syn_chwniso A) (.cv v))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chwniso A) C)) p0019 p0023
  have p0025 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) hyp_hwnisoclasseqbcl_1
  have p0026 :=
    @g_id (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0027 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0025 p0026
  have p0028 :=
    @g_hwnisoclasseqb v u A
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) p0027 p0028
  have p0030 :=
    @g_vtocl2g (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr B (syn_chwniso A) (.cv v)))) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chwniso A) C))) u v B C (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0015 p0024 p0029
  have p0031 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chwniso A) C))) p0006 p0030
  have p0032 :=
    @g_pm2_43i (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wb (.classEq (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chwniso A) C)) p0031
  exact p0032

noncomputable def g_hnwcutcodecncl
    (B : Class) (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutcodecncl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))) := by
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
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex B D
  have p0001 :=
    @g_eleq1 (.cv x) B D
  have p0002 :=
    @g_hnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0003 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B) (syn_chwcn D) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0001 p0003
  have p0005 :=
    @g_hnwcutcodecn x D R dv_cache_0002 hyp_hnwcutcodecncl_1
  have p0006 :=
    @g_vtoclg (.imp (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))) (.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))) x B (syn_cvv) dv_cache_0003 dv_cache_0004 p0004 p0005
  have p0007 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0000 p0006
  exact p0007

noncomputable def g_hnwcutclassltne
    (x : Var) (y : Var) (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutclassltne_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_a1i (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) hyp_hnwcutclassltne_1
  have p0001 :=
    @g_simpl (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0002 :=
    @g_jca (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0004 :=
    @g_jca (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0002 p0003
  have p0005 :=
    @g_hnwcutcodeltnoiso x y D R
  have p0006 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))) p0004 p0005
  have p0007 :=
    @g_simpr (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0008 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))
  have p0009 :=
    @g_ssel (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) D (.cv x)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.classMem (.cv x) D) p0007 p0010
  have p0012 :=
    @g_hnwcutcodecncl (.cv x) D R dv_cache_0001 hyp_hnwcutclassltne_1
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) p0011 p0012
  have p0014 :=
    @g_simpl (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0015 :=
    @g_hnwcutcodecncl (.cv y) D R dv_cache_0001 hyp_hnwcutclassltne_1
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (.cv y) D) (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)) p0014 p0015
  have p0017 :=
    @g_jca (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)) p0013 p0016
  have p0018 :=
    @g_brex R D (syn_cwe)
  have p0019 :=
    @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0020 :=
    @g_syl (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) (.classMem D (syn_cvv)) p0018 p0019
  have p0021 :=
    Nominal.mp hyp_hnwcutclassltne_1 p0020
  have p0022 :=
    @g_hwnisoclasseqbcl D (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D (.cv y)) p0021
  have p0023 :=
    @g_syl (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D))) (syn_wb (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))) p0017 p0022
  have p0024 :=
    @g_biimpd (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))) p0023
  have p0025 :=
    @g_con3d (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))) p0024
  have p0026 :=
    @g_mpd (syn_wa (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) p0006 p0025
  exact p0026

#print axioms g_hnwcutclassltne

end NFChoice.DirectNominalPrf.WPPReplay
