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
import NominalWPPReplayChunk014Compact001Part012

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

noncomputable def g_fdpivmap2val
    (A : Class) (B : Class) (R : Class) (p : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_p : p ∉ A.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) (hyp_fdpivmap2val_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdpivmap2val_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdpivmap2val_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv p) (syn_cxpk B B)) (.classEq (syn_cfv (syn_cfdpivmap2 R A B) (.cv p)) (syn_cfdminvalp R A B (.cv p)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ ({p} : Finset Var)
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv p)).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (A).fv from (by exact dv_A_p))))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((B).fv) (({p} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show p ∉ (B).fv from (by exact dv_B_p))))))
  have dv_cache_0005 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint ((Class.cv p)).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint ((Class.cv p)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({p} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show p ∉ (R).fv from (by exact dv_R_p))))))
  have dv_cache_0007 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((syn_cxpk B B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem (.cv p) (syn_cxpk B B))
  have p0001 :=
    @g_fdminvalpex A B (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_fdpivmap2val_1 hyp_fdpivmap2val_2 hyp_fdpivmap2val_3
  have p0002 :=
    @g_a1i (.classMem (syn_cfdminvalp R A B (.cv p)) (syn_cvv)) (.classMem (.cv p) (syn_cxpk B B)) p0001
  have p0003 :=
    @g_jca (.classMem (.cv p) (syn_cxpk B B)) (.classMem (.cv p) (syn_cxpk B B)) (.classMem (syn_cfdminvalp R A B (.cv p)) (syn_cvv)) p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p dv_cache_0001 dv_cache_0003 dv_cache_0007 dv_cache_0005 dv_cache_0008 dv_cache_0009
  have p0005 :=
    @g_fvmpt2 p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)) (syn_cvv) (syn_cfdpivmap2 R A B) dv_cache_0010 p0004
  have p0006 :=
    @g_syl (.classMem (.cv p) (syn_cxpk B B)) (syn_wa (.classMem (.cv p) (syn_cxpk B B)) (.classMem (syn_cfdminvalp R A B (.cv p)) (syn_cvv))) (.classEq (syn_cfv (syn_cfdpivmap2 R A B) (.cv p)) (syn_cfdminvalp R A B (.cv p))) p0003 p0005
  exact p0006

noncomputable def g_fdpivrange2br
    (A : Class) (B : Class) (C : Class) (R : Class) (p : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_p : p ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_p : p ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_p : p ∉ C.fv) (dv_R_p : p ∉ R.fv) (hyp_fdpivrange2br_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdpivrange2br_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdpivrange2br_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem C (syn_cfdpivrange2 R A B)) (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ ({p} : Finset Var)
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0004 : p ∉ ((syn_cxpk B B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_cfdpivmap2 R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_p, dv_B_p, dv_R_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cfdpivrange2] using (Nominal.classEqRefl (syn_cfdpivrange2 R A B)))
  have p0001 :=
    @g_eleq2i (syn_cfdpivrange2 R A B) (syn_crn (syn_cfdpivmap2 R A B)) C p0000
  have p0002 :=
    @g_fdpivmap2fn A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdpivrange2br_1 hyp_fdpivrange2br_2 hyp_fdpivrange2br_3
  have p0003 :=
    @g_fvelrnb p (syn_cxpk B B) C (syn_cfdpivmap2 R A B) dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_fdpivmap2val A B R p dv_cache_0001 dv_cache_0002 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009 hyp_fdpivrange2br_1 hyp_fdpivrange2br_2 hyp_fdpivrange2br_3
  have p0006 :=
    @g_eqeq1d (.classMem (.cv p) (syn_cxpk B B)) (syn_cfv (syn_cfdpivmap2 R A B) (.cv p)) (syn_cfdminvalp R A B (.cv p)) C p0005
  have p0007 :=
    @g_rexbiia (.classEq (syn_cfv (syn_cfdpivmap2 R A B) (.cv p)) C) (.classEq (syn_cfdminvalp R A B (.cv p)) C) p (syn_cxpk B B) p0006
  have p0008 :=
    @g_bitri (.classMem C (syn_crn (syn_cfdpivmap2 R A B))) (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfv (syn_cfdpivmap2 R A B) (.cv p)) C)) (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) C)) p0004 p0007
  have p0009 :=
    @g_bitri (.classMem C (syn_cfdpivrange2 R A B)) (.classMem C (syn_crn (syn_cfdpivmap2 R A B))) (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) C)) p0001 p0008
  exact p0009

noncomputable def g_fdminvalpss
    (A : Class) (B : Class) (C : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) (hyp_fdminvalpss_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wss (syn_cfdminvalp R A B C) A) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0009 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((syn_cfdminvalp R A B C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_C, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdminvalpbr z A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 hyp_fdminvalpss_1
  have p0001 :=
    @g_biimpi (.classMem (.cv z) (syn_cfdminvalp R A B C)) (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfdminsep R A B)) p0000
  have p0002 :=
    (by simpa [syn_cfdminsep] using (Nominal.classEqRefl (syn_cfdminsep R A B)))
  have p0003 :=
    @g_difss (syn_cfdsep A B) (syn_cfdnonmin R A B)
  have p0004 :=
    @g_eqsstri (syn_cfdminsep R A B) (syn_cdif (syn_cfdsep A B) (syn_cfdnonmin R A B)) (syn_cfdsep A B) p0002 p0003
  have p0005 :=
    (by simpa [syn_cfdsep] using (Nominal.classEqRefl (syn_cfdsep A B)))
  have p0006 :=
    (by simpa [syn_csymdif] using (Nominal.classEqRefl (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B))))
  have p0007 :=
    @g_eqtri (syn_cfdsep A B) (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B)) (syn_cun (syn_cdif (syn_cfde0 A B) (syn_cfde1 A B)) (syn_cdif (syn_cfde1 A B) (syn_cfde0 A B))) p0005 p0006
  have p0008 :=
    @g_difss (syn_cfde0 A B) (syn_cfde1 A B)
  have p0009 :=
    (by simpa [syn_cfde0] using (Nominal.classEqRefl (syn_cfde0 A B)))
  have p0010 :=
    @g_inss2 (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)
  have p0011 :=
    @g_eqsstri (syn_cfde0 A B) (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)) (syn_cfddom A B) p0009 p0010
  have p0012 :=
    @g_sstri (syn_cdif (syn_cfde0 A B) (syn_cfde1 A B)) (syn_cfde0 A B) (syn_cfddom A B) p0008 p0011
  have p0013 :=
    @g_difss (syn_cfde1 A B) (syn_cfde0 A B)
  have p0014 :=
    (by simpa [syn_cfde1] using (Nominal.classEqRefl (syn_cfde1 A B)))
  have p0015 :=
    @g_inss2 (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B)
  have p0016 :=
    @g_eqsstri (syn_cfde1 A B) (syn_cin (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B)) (syn_cfddom A B) p0014 p0015
  have p0017 :=
    @g_sstri (syn_cdif (syn_cfde1 A B) (syn_cfde0 A B)) (syn_cfde1 A B) (syn_cfddom A B) p0013 p0016
  have p0018 :=
    @g_unssi (syn_cdif (syn_cfde0 A B) (syn_cfde1 A B)) (syn_cdif (syn_cfde1 A B) (syn_cfde0 A B)) (syn_cfddom A B) p0012 p0017
  have p0019 :=
    @g_eqsstri (syn_cfdsep A B) (syn_cun (syn_cdif (syn_cfde0 A B) (syn_cfde1 A B)) (syn_cdif (syn_cfde1 A B) (syn_cfde0 A B))) (syn_cfddom A B) p0007 p0018
  have p0020 :=
    @g_sstri (syn_cfdminsep R A B) (syn_cfdsep A B) (syn_cfddom A B) p0004 p0019
  have p0021 :=
    @g_sseli (syn_cfdminsep R A B) (syn_cfddom A B) (syn_copk (syn_csn (.cv z)) C) p0020
  have p0022 :=
    @g_syl (.classMem (.cv z) (syn_cfdminvalp R A B C)) (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfdminsep R A B)) (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfddom A B)) p0001 p0021
  have p0023 :=
    (by simpa [syn_cfddom] using (Nominal.classEqRefl (syn_cfddom A B)))
  have p0024 :=
    @g_eleq2i (syn_cfddom A B) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)) (syn_copk (syn_csn (.cv z)) C) p0023
  have p0025 :=
    @g_snex (.cv z)
  have p0026 :=
    @g_opkelxpk (syn_csn (.cv z)) C (syn_cpw1 A) (syn_cxpk B B) p0025 hyp_fdminvalpss_1
  have p0027 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfddom A B)) (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B))) (syn_wa (.classMem (syn_csn (.cv z)) (syn_cpw1 A)) (.classMem C (syn_cxpk B B))) p0024 p0026
  have p0028 :=
    @g_simplbi (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfddom A B)) (.classMem (syn_csn (.cv z)) (syn_cpw1 A)) (.classMem C (syn_cxpk B B)) p0027
  have p0029 :=
    @g_snelpw1 (.cv z) A
  have p0030 :=
    @g_biimpi (.classMem (syn_csn (.cv z)) (syn_cpw1 A)) (.classMem (.cv z) A) p0029
  have p0031 :=
    @g_n_3syl (.classMem (.cv z) (syn_cfdminvalp R A B C)) (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfddom A B)) (.classMem (syn_csn (.cv z)) (syn_cpw1 A)) (.classMem (.cv z) A) p0022 p0028 p0030
  have p0032 :=
    @g_ssriv z (syn_cfdminvalp R A B C) A dv_cache_0011 dv_cache_0004 p0031
  exact p0032

noncomputable def g_elfpiv
    (A : Class) (B : Class) (C : Class) (R : Class) (e : Var) (c : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (dv_A_e : e ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_c : c ∉ B.fv) (dv_B_e : e ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_c : c ∉ C.fv) (dv_C_e : e ∉ C.fv) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf (syn_wb (.classMem (.cv e) (syn_cfpiv R A B C)) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 B C))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c)))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ ({e} : Finset Var) ∪ ({c} : Finset Var)
  let b : Var := freshVar proofSupport 0
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_e : b ≠ e := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_e_ne_b : e ≠ b :=
    Ne.symm fresh_b_ne_e
  have fresh_b_ne_c : b ≠ c := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have dv_cache_0001 : c ∉ ((Wff.classEq (.cv b) (.cv e))).fv := by
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_b, dv_c_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint (A).fv (B).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0003 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0004 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : c ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0008 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0009 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : c ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0012 : b ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : c ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : b ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : c ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : b ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0017 : b ∉ ((Class.cv e)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((syn_wa (.classMem (.cv e) (syn_csep2 B C)) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_e, fresh_b_not_B, fresh_b_not_C, fresh_b_not_A, fresh_b_ne_c, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv b) (.cv e))
  have p0001 :=
    @g_eleq1d (.classEq (.cv b) (.cv e)) (.cv b) (.cv e) (syn_csep2 B C) p0000
  have p0002 :=
    @g_id (.classEq (.cv b) (.cv e))
  have p0003 :=
    @g_breq1d (.classEq (.cv b) (.cv e)) (.cv b) (.cv e) (.cv c) R p0002
  have p0004 :=
    @g_imbi2d (.classEq (.cv b) (.cv e)) (syn_wbr (.cv b) R (.cv c)) (syn_wbr (.cv e) R (.cv c)) (.classMem (.cv c) (syn_csep2 B C)) p0003
  have p0005 :=
    @g_ralbidv (.classEq (.cv b) (.cv e)) (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv b) R (.cv c))) (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c))) c A dv_cache_0001 p0004
  have p0006 :=
    @g_anbi12d (.classEq (.cv b) (.cv e)) (.classMem (.cv b) (syn_csep2 B C)) (.classMem (.cv e) (syn_csep2 B C)) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv b) R (.cv c)))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c)))) p0001 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fpiv A B C R b c dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0008 :=
    @g_elrab2 (syn_wa (.classMem (.cv b) (syn_csep2 B C)) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv b) R (.cv c))))) (syn_wa (.classMem (.cv e) (syn_csep2 B C)) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c))))) b (.cv e) A (syn_cfpiv R A B C) dv_cache_0017 dv_cache_0005 dv_cache_0018 p0006 p0007
  have p0009 :=
    @g_anass (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 B C)) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c))))
  have p0010 :=
    @g_bitr4i (.classMem (.cv e) (syn_cfpiv R A B C)) (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem (.cv e) (syn_csep2 B C)) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c)))))) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 B C))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c))))) p0008 p0009
  exact p0010

noncomputable def g_fdminsepval0J
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (e : Var) (c : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (dv_A_e : e ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_c : c ∉ B.fv) (dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_c : c ∉ C.fv) (dv_C_e : e ∉ C.fv) (dv_D_R : Disjoint D.fv R.fv) (dv_D_c : c ∉ D.fv) (dv_D_e : e ∉ D.fv) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf (.imp (syn_wa (.classMem C B) (.classMem D B)) (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B)) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({e} : Finset Var) ∪ ({c} : Finset Var)
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : e ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0007 : e ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0009 : e ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : e ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0012 : c ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0014 : c ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0016 : c ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0018 : c ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : c ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : e ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : c ≠ e := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show c ≠ e from (by exact dv_c_e))
  have p0000 :=
    (by simpa [syn_cfdminsep] using (Nominal.classEqRefl (syn_cfdminsep R A B)))
  have p0001 :=
    @g_eleq2i (syn_cfdminsep R A B) (syn_cdif (syn_cfdsep A B) (syn_cfdnonmin R A B)) (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0000
  have p0002 :=
    @g_eldif (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B) (syn_cfdnonmin R A B)
  have p0003 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cdif (syn_cfdsep A B) (syn_cfdnonmin R A B))) (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)))) p0001 p0002
  have p0004 :=
    @g_a1i (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B)) (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))))) (syn_wa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @g_fdsepvalJ A B C D e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0006 :=
    @g_fdnonminval0J A B C D R e c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0011 dv_cache_0012 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0013 dv_cache_0014 dv_cache_0007 dv_cache_0008 dv_cache_0015 dv_cache_0016 dv_cache_0009 dv_cache_0017 dv_cache_0018 dv_cache_0010 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0007 :=
    @g_notbid (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)) (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))) p0006
  have p0008 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))) p0005 p0007
  have p0009 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B)) (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)))) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))))) p0004 p0008
  exact p0009

noncomputable def g_wppwepo
    (A : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cpartial) A)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0001 :=
    @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 :=
    @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A) (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A) p0003
  have p0005 :=
    @g_sopc A R
  have p0006 :=
    @g_simplbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A) p0005
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A) p0004 p0006
  exact p0007

noncomputable def g_wppweref
    (A : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cref) A)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0001 :=
    @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 :=
    @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A) (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A) p0003
  have p0005 :=
    @g_sopc A R
  have p0006 :=
    @g_simplbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A) p0005
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A) p0004 p0006
  have p0008 :=
    @g_porta A R
  have p0009 :=
    @g_simp1bi (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A) p0008
  have p0010 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A) p0007 p0009
  exact p0010

noncomputable def g_wppweconnex
    (A : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cconnex) A)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0001 :=
    @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 :=
    @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A) (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A) p0003
  have p0005 :=
    @g_sopc A R
  have p0006 :=
    @g_simprbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A) p0005
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cconnex) A) p0004 p0006
  exact p0007

noncomputable def g_wppweantisym
    (A : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cantisym) A)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0001 :=
    @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 :=
    @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A) (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A) p0003
  have p0005 :=
    @g_sopc A R
  have p0006 :=
    @g_simplbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A) p0005
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A) p0004 p0006
  have p0008 :=
    @g_porta A R
  have p0009 :=
    @g_simp3bi (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A) p0008
  have p0010 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cantisym) A) p0007 p0009
  exact p0010

#print axioms g_wppweantisym

end NFChoice.DirectNominalPrf.WPPReplay
