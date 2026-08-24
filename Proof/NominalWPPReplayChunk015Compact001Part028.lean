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
import NominalWPPReplayChunk015Compact001Part027

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

noncomputable def g_lnpwquofnrawexact
    (D : Class) (R : Class) (hyp_lnpwquofnrawexact_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwquofnrawexact_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) (syn_cqs D (syn_clnker R))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let c : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let s : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  let x : Var := freshVar proofSupport 4
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (h))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_c_ne_z : c ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_c : z ≠ c :=
    Ne.symm fresh_c_ne_z
  have fresh_c_ne_s : c ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_s_ne_c : s ≠ c :=
    Ne.symm fresh_c_ne_s
  have fresh_c_ne_p : c ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_c : p ≠ c :=
    Ne.symm fresh_c_ne_p
  have fresh_c_ne_x : c ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have fresh_z_ne_s : z ≠ s := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_s_ne_z : s ≠ z :=
    Ne.symm fresh_z_ne_s
  have fresh_z_ne_p : z ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_s_ne_p : s ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_s : p ≠ s :=
    Ne.symm fresh_s_ne_p
  have fresh_s_ne_x : s ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_x_ne_s : x ≠ s :=
    Ne.symm fresh_s_ne_x
  have fresh_p_ne_x : p ≠ x := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have dv_cache_0001 : z ∉ ((Class.cv c)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_clnpwclassfn)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_csn (syn_cop R D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_csn (syn_cop R D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((syn_csn (syn_cop R D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_R, fresh_s_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : s ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((Wff.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_z, fresh_p_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : s ∉ ((Wff.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_z, fresh_s_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Wff.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_s, fresh_z_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show z ≠ p from (by exact fresh_z_ne_p))
  have dv_cache_0014 : z ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show z ≠ s from (by exact fresh_z_ne_s))
  have dv_cache_0015 : p ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show p ≠ s from (by exact fresh_p_ne_s))
  have dv_cache_0016 : s ∉ ((Wff.classEq (.cv p) (syn_cop R D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_p, fresh_s_not_R, fresh_s_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((syn_cop R D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_wrex s (syn_cpw1 D) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_D, fresh_p_not_R, fresh_p_ne_s, fresh_p_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((Wff.imp (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)) (.classMem (.cv c) (syn_cqs D (syn_clnker R))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cqs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_D, fresh_x_ne_s, fresh_x_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : s ∉ ((Wff.classMem (.cv c) (syn_cqs D (syn_clnker R)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cqs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_c, fresh_s_not_D, fresh_s_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : c ∉ ((syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, fresh_c_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : c ∉ ((syn_cqs D (syn_clnker R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cqs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_D, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : x ∉ ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((syn_clnker R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((Wff.classMem (.cv c) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_lnpwclassfnfn
  have p0001 :=
    @g_fnfun (syn_cvv) (syn_clnpwclassfn)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_fvelima z (.cv c) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_clnpwclassfn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_mpan (syn_wfun (syn_clnpwclassfn)) (.classMem (.cv c) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))) (syn_wrex z (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c))) p0002 p0003
  have p0005 :=
    @g_id (.classEq (.cv z) (syn_cop (.cv p) (.cv s)))
  have p0006 :=
    @g_fveq2d (.classEq (.cv z) (syn_cop (.cv p) (.cv s))) (.cv z) (syn_cop (.cv p) (.cv s)) (syn_clnpwclassfn) p0005
  have p0007 :=
    @g_eqeq1d (.classEq (.cv z) (syn_cop (.cv p) (.cv s))) (syn_cfv (syn_clnpwclassfn) (.cv z)) (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c) p0006
  have p0008 :=
    @g_rexxp (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c)) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c)) z p s (syn_csn (syn_cop R D)) (syn_cpw1 D) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0007
  have p0009 :=
    @g_opex R D hyp_lnpwquofnrawexact_1 hyp_lnpwquofnrawexact_2
  have p0010 :=
    @g_id (.classEq (.cv p) (syn_cop R D))
  have p0011 :=
    @g_opeq1d (.classEq (.cv p) (syn_cop R D)) (.cv p) (syn_cop R D) (.cv s) p0010
  have p0012 :=
    @g_fveq2d (.classEq (.cv p) (syn_cop R D)) (syn_cop (.cv p) (.cv s)) (syn_cop (syn_cop R D) (.cv s)) (syn_clnpwclassfn) p0011
  have p0013 :=
    @g_eqeq1d (.classEq (.cv p) (syn_cop R D)) (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c) p0012
  have p0014 :=
    @g_rexbidv (.classEq (.cv p) (syn_cop R D)) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c)) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)) s (syn_cpw1 D) dv_cache_0016 p0013
  have p0015 :=
    @g_rexsn (syn_wrex s (syn_cpw1 D) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c))) (syn_wrex s (syn_cpw1 D) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) p (syn_cop R D) dv_cache_0017 dv_cache_0018 p0009 p0014
  have p0016 :=
    @g_bitri (syn_wrex z (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c))) (syn_wrex p (syn_csn (syn_cop R D)) (syn_wrex s (syn_cpw1 D) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c)))) (syn_wrex s (syn_cpw1 D) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) p0008 p0015
  have p0017 :=
    @g_elpw1 x (.cv s) D dv_cache_0019 dv_cache_0020
  have p0018 :=
    @g_n_3simpc (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
  have p0019 :=
    @g_simpr (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
  have p0020 :=
    @g_syl (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (syn_wa (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)) p0018 p0019
  have p0021 :=
    @g_eqcomd (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c) p0020
  have p0022 :=
    @g_n_3simpa (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
  have p0023 :=
    @g_simpr (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
  have p0024 :=
    @g_syl (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (syn_wa (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))) (.classEq (.cv s) (syn_csn (.cv x))) p0022 p0023
  have p0025 :=
    @g_id (.classEq (.cv s) (syn_csn (.cv x)))
  have p0026 :=
    @g_opeq2d (.classEq (.cv s) (syn_csn (.cv x))) (.cv s) (syn_csn (.cv x)) (syn_cop R D) p0025
  have p0027 :=
    @g_fveq2d (.classEq (.cv s) (syn_csn (.cv x))) (syn_cop (syn_cop R D) (.cv s)) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clnpwclassfn) p0026
  have p0028 :=
    @g_vex x
  have p0029 :=
    @g_lnpwclassfnsnval D R (.cv x) hyp_lnpwquofnrawexact_1 hyp_lnpwquofnrawexact_2 p0028
  have p0030 :=
    @g_syl6eq (.classEq (.cv s) (syn_csn (.cv x))) (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cec (.cv x) (syn_clnker R)) p0027 p0029
  have p0031 :=
    @g_syl (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (syn_cec (.cv x) (syn_clnker R))) p0024 p0030
  have p0032 :=
    @g_eqcomd (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (syn_cec (.cv x) (syn_clnker R)) p0031
  have p0033 :=
    @g_eqtr4d (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (.cv c) (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (syn_cec (.cv x) (syn_clnker R)) p0021 p0032
  have p0034 :=
    @g_n_3simpa (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
  have p0035 :=
    @g_simpl (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
  have p0036 :=
    @g_syl (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (syn_wa (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))) (.classMem (.cv x) D) p0034 p0035
  have p0037 :=
    @g_lnkerex R hyp_lnpwquofnrawexact_1
  have p0038 :=
    @g_ecelqsi D (.cv x) (syn_clnker R) p0037
  have p0039 :=
    @g_syl (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (.classMem (.cv x) D) (.classMem (syn_cec (.cv x) (syn_clnker R)) (syn_cqs D (syn_clnker R))) p0036 p0038
  have p0040 :=
    @g_eqeltrd (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (.cv c) (syn_cec (.cv x) (syn_clnker R)) (syn_cqs D (syn_clnker R)) p0033 p0039
  have p0041 :=
    @g_n_3exp (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)) (.classMem (.cv c) (syn_cqs D (syn_clnker R))) p0040
  have p0042 :=
    @g_rexlimiv (.classEq (.cv s) (syn_csn (.cv x))) (.imp (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)) (.classMem (.cv c) (syn_cqs D (syn_clnker R)))) x D dv_cache_0021 p0041
  have p0043 :=
    @g_sylbi (.classMem (.cv s) (syn_cpw1 D)) (syn_wrex x D (.classEq (.cv s) (syn_csn (.cv x)))) (.imp (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)) (.classMem (.cv c) (syn_cqs D (syn_clnker R)))) p0017 p0042
  have p0044 :=
    @g_rexlimiv (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)) (.classMem (.cv c) (syn_cqs D (syn_clnker R))) s (syn_cpw1 D) dv_cache_0022 p0043
  have p0045 :=
    @g_sylbi (syn_wrex z (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c))) (syn_wrex s (syn_cpw1 D) (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))) (.classMem (.cv c) (syn_cqs D (syn_clnker R))) p0016 p0044
  have p0046 :=
    @g_syl (.classMem (.cv c) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))) (syn_wrex z (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c))) (.classMem (.cv c) (syn_cqs D (syn_clnker R))) p0004 p0045
  have p0047 :=
    @g_ssriv c (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) (syn_cqs D (syn_clnker R)) dv_cache_0023 dv_cache_0024 p0046
  have p0048 :=
    @g_eqid (syn_cqs D (syn_clnker R))
  have p0049 :=
    @g_id (.classEq (syn_cec (.cv x) (syn_clnker R)) (.cv c))
  have p0050 :=
    @g_eleq1d (.classEq (syn_cec (.cv x) (syn_clnker R)) (.cv c)) (syn_cec (.cv x) (syn_clnker R)) (.cv c) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0049
  have p0051 :=
    @g_vex x
  have p0052 :=
    @g_lnpwclassfnsnval D R (.cv x) hyp_lnpwquofnrawexact_1 hyp_lnpwquofnrawexact_2 p0051
  have p0053 :=
    @g_a1i (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cec (.cv x) (syn_clnker R))) (.classMem (.cv x) D) p0052
  have p0054 :=
    @g_opex R D hyp_lnpwquofnrawexact_1 hyp_lnpwquofnrawexact_2
  have p0055 :=
    @g_snid (syn_cop R D) p0054
  have p0056 :=
    @g_a1i (.classMem (syn_cop R D) (syn_csn (syn_cop R D))) (.classMem (.cv x) D) p0055
  have p0057 :=
    @g_id (.classMem (.cv x) D)
  have p0058 :=
    @g_snelpw1 (.cv x) D
  have p0059 :=
    @g_sylibr (.classMem (.cv x) D) (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0057 p0058
  have p0060 :=
    @g_jca (.classMem (.cv x) D) (.classMem (syn_cop R D) (syn_csn (syn_cop R D))) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0056 p0059
  have p0061 :=
    @g_opelxp (syn_cop R D) (syn_csn (.cv x)) (syn_csn (syn_cop R D)) (syn_cpw1 D)
  have p0062 :=
    @g_sylibr (.classMem (.cv x) D) (syn_wa (.classMem (syn_cop R D) (syn_csn (syn_cop R D))) (.classMem (syn_csn (.cv x)) (syn_cpw1 D))) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0060 p0061
  have p0063 :=
    @g_lnpwclassfnfn
  have p0064 :=
    @g_fnfun (syn_cvv) (syn_clnpwclassfn)
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_opex R D hyp_lnpwquofnrawexact_1 hyp_lnpwquofnrawexact_2
  have p0067 :=
    @g_snex (.cv x)
  have p0068 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0066 p0067
  have p0069 :=
    @g_lnpwclassfnfn
  have p0070 :=
    @g_fndm (syn_cvv) (syn_clnpwclassfn)
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_eleqtrri (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv) (syn_cdm (syn_clnpwclassfn)) p0068 p0071
  have p0073 :=
    @g_pm3_2i (syn_wfun (syn_clnpwclassfn)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cdm (syn_clnpwclassfn))) p0065 p0072
  have p0074 :=
    @g_funfvima (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clnpwclassfn)
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_syl (.classMem (.cv x) D) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) (.classMem (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))) p0062 p0075
  have p0077 :=
    @g_eqeltrrd (.classMem (.cv x) D) (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cec (.cv x) (syn_clnker R)) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0053 p0076
  have p0078 :=
    @g_ectocl (.classMem (syn_cec (.cv x) (syn_clnker R)) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))) (.classMem (.cv c) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))) x (.cv c) D (syn_clnker R) (syn_cqs D (syn_clnker R)) dv_cache_0025 dv_cache_0020 dv_cache_0026 dv_cache_0027 p0048 p0050 p0077
  have p0079 :=
    @g_ssriv c (syn_cqs D (syn_clnker R)) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) dv_cache_0024 dv_cache_0023 p0078
  have p0080 :=
    @g_eqssi (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) (syn_cqs D (syn_clnker R)) p0047 p0079
  exact p0080

noncomputable def g_lnpwquofnval
    (D : Class) (R : Class) (hyp_lnpwquofnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwquofnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D))) (syn_cqs D (syn_clnker R))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    @g_lnpwquofnrawval D R hyp_lnpwquofnval_1 hyp_lnpwquofnval_2
  have p0001 :=
    @g_lnpwquofnrawexact D R hyp_lnpwquofnval_1 hyp_lnpwquofnval_2
  have p0002 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D))) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) (syn_cqs D (syn_clnker R)) p0000 p0001
  exact p0002

noncomputable def g_lnpairraisefnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnpairraisefn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1stex
  have p0001 :=
    @g_wppimagefn (syn_c1st) p0000
  have p0002 :=
    @g_n_2ndex
  have p0003 :=
    @g_wppimagefn (syn_c2nd) p0002
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cimage (syn_c2nd)) (syn_cvv)) p0001 p0003
  have p0005 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_inidm (syn_cvv)
  have p0008 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) p0007
  have p0009 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0006 p0008
  have p0010 :=
    (by simpa [syn_clnpairraisefn] using (Nominal.classEqRefl (syn_clnpairraisefn)))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clnpairraisefn) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clnpairraisefn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0009 p0011
  exact p0012

noncomputable def g_lnpairraisefnval
    (X : Class) (Y : Class) (hyp_lnpairraisefnval_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_lnpairraisefnval_2 : Nominal.NPrf (.classMem Y (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop X Y))) (syn_cop (syn_csn X) (syn_csn Y))) := by
  let proofSupport : Finset Var := X.fv ∪ Y.fv
  have dv_cache_0001 : Disjoint ((syn_csn (syn_cop X Y))).fv ((syn_c1st)).fv := by
    exact (show Disjoint ((syn_csn (syn_cop X Y))).fv ((syn_c1st)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint (((syn_cop X Y)).fv) ((∅ : Finset Var)) from (by simp))))
  have dv_cache_0002 : Disjoint ((syn_csn (syn_cop X Y))).fv ((syn_c2nd)).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((syn_csn (syn_cop X Y))).fv ((syn_c2nd)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd]; exact (show Disjoint (((syn_cop X Y)).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 :=
    (by simpa [syn_clnpairraisefn] using (Nominal.classEqRefl (syn_clnpairraisefn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop X Y)) (syn_clnpairraisefn) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) p0000
  have p0002 :=
    @g_eqid (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))
  have p0003 :=
    @g_n_1stex
  have p0004 :=
    @g_wppimagefn (syn_c1st) p0003
  have p0005 :=
    @g_snex (syn_cop X Y)
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c1st)) (syn_cvv)) (.classMem (syn_csn (syn_cop X Y)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_fnbrfvb (syn_cvv) (syn_csn (syn_cop X Y)) (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_cimage (syn_c1st))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbi (.classEq (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))) (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c1st)) (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))) p0002 p0008
  have p0010 :=
    @g_eqid (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))
  have p0011 :=
    @g_n_2ndex
  have p0012 :=
    @g_wppimagefn (syn_c2nd) p0011
  have p0013 :=
    @g_snex (syn_cop X Y)
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c2nd)) (syn_cvv)) (.classMem (syn_csn (syn_cop X Y)) (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_fnbrfvb (syn_cvv) (syn_csn (syn_cop X Y)) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))) (syn_cimage (syn_c2nd))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_mpbi (.classEq (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))) (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c2nd)) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))) p0010 p0016
  have p0018 :=
    @g_pm3_2i (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c1st)) (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))) (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c2nd)) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))) p0009 p0017
  have p0019 :=
    @g_trtxp (syn_csn (syn_cop X Y)) (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))) (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))
  have p0020 :=
    @g_mpbir (syn_wbr (syn_csn (syn_cop X Y)) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cop (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))))) (syn_wa (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c1st)) (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))) (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c2nd)) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))))) p0018 p0019
  have p0021 :=
    @g_n_1stex
  have p0022 :=
    @g_wppimagefn (syn_c1st) p0021
  have p0023 :=
    @g_n_2ndex
  have p0024 :=
    @g_wppimagefn (syn_c2nd) p0023
  have p0025 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cimage (syn_c2nd)) (syn_cvv)) p0022 p0024
  have p0026 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_inidm (syn_cvv)
  have p0029 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) p0028
  have p0030 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0027 p0029
  have p0031 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_funbrfv (syn_csn (syn_cop X Y)) (syn_cop (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    Nominal.mp p0020 p0034
  have p0036 :=
    @g_n_1stex
  have p0037 :=
    @g_snex (syn_cop X Y)
  have p0038 :=
    @g_wppfvimage (syn_csn (syn_cop X Y)) (syn_c1st) dv_cache_0001 p0036 p0037
  have p0039 :=
    @g_dfdm4 (syn_csn (syn_cop X Y))
  have p0040 :=
    @g_eqcomi (syn_cdm (syn_csn (syn_cop X Y))) (syn_cima (syn_c1st) (syn_csn (syn_cop X Y))) p0039
  have p0041 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_cima (syn_c1st) (syn_csn (syn_cop X Y))) (syn_cdm (syn_csn (syn_cop X Y))) p0038 p0040
  have p0042 :=
    @g_dmsnop X Y hyp_lnpairraisefnval_2
  have p0043 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_cdm (syn_csn (syn_cop X Y))) (syn_csn X) p0041 p0042
  have p0044 :=
    @g_n_2ndex
  have p0045 :=
    @g_snex (syn_cop X Y)
  have p0046 :=
    @g_wppfvimage (syn_csn (syn_cop X Y)) (syn_c2nd) dv_cache_0002 p0044 p0045
  have p0047 :=
    @g_dfrn5 (syn_csn (syn_cop X Y))
  have p0048 :=
    @g_eqcomi (syn_crn (syn_csn (syn_cop X Y))) (syn_cima (syn_c2nd) (syn_csn (syn_cop X Y))) p0047
  have p0049 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))) (syn_cima (syn_c2nd) (syn_csn (syn_cop X Y))) (syn_crn (syn_csn (syn_cop X Y))) p0046 p0048
  have p0050 :=
    @g_rnsnop X Y hyp_lnpairraisefnval_1
  have p0051 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))) (syn_crn (syn_csn (syn_cop X Y))) (syn_csn Y) p0049 p0050
  have p0052 :=
    @g_opeq12i (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_csn X) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))) (syn_csn Y) p0043 p0051
  have p0053 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_csn (syn_cop X Y))) (syn_cop (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))) (syn_cop (syn_csn X) (syn_csn Y)) p0035 p0052
  have p0054 :=
    @g_eqtri (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop X Y))) (syn_cfv (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_csn (syn_cop X Y))) (syn_cop (syn_csn X) (syn_csn Y)) p0001 p0053
  exact p0054

noncomputable def g_lnsifnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnsifn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnpairraisefn] using (Nominal.classEqRefl (syn_clnpairraisefn)))
  have p0001 :=
    @g_n_1stex
  have p0002 :=
    @g_imageex (syn_c1st) p0001
  have p0003 :=
    @g_n_2ndex
  have p0004 :=
    @g_imageex (syn_c2nd) p0003
  have p0005 :=
    @g_txpex (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)) p0002 p0004
  have p0006 :=
    @g_eqeltri (syn_clnpairraisefn) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv) p0000 p0005
  have p0007 :=
    @g_wppimagefn (syn_clnpairraisefn) p0006
  have p0008 :=
    @g_fnfullfun (syn_cpw1fn)
  have p0009 :=
    @g_fncovv (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn)) p0007 p0008
  have p0010 :=
    (by simpa [syn_clnsifn] using (Nominal.classEqRefl (syn_clnsifn)))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clnsifn) (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clnsifn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) (syn_cvv)) p0009 p0011
  exact p0012

noncomputable def g_lnsifnex
     :
    Nominal.NPrf (.classMem (syn_clnsifn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnsifn] using (Nominal.classEqRefl (syn_clnsifn)))
  have p0001 :=
    (by simpa [syn_clnpairraisefn] using (Nominal.classEqRefl (syn_clnpairraisefn)))
  have p0002 :=
    @g_n_1stex
  have p0003 :=
    @g_imageex (syn_c1st) p0002
  have p0004 :=
    @g_n_2ndex
  have p0005 :=
    @g_imageex (syn_c2nd) p0004
  have p0006 :=
    @g_txpex (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)) p0003 p0005
  have p0007 :=
    @g_eqeltri (syn_clnpairraisefn) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv) p0001 p0006
  have p0008 :=
    @g_imageex (syn_clnpairraisefn) p0007
  have p0009 :=
    @g_pw1fnex
  have p0010 :=
    @g_fullfunex (syn_cpw1fn) p0009
  have p0011 :=
    @g_coex (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn)) p0008 p0010
  have p0012 :=
    @g_eqeltri (syn_clnsifn) (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) (syn_cvv) p0000 p0011
  exact p0012

noncomputable def g_lnsifnrawval
    (R : Class) (hyp_lnsifnrawval_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnsifn) (syn_csn R)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) := by
  let proofSupport : Finset Var := R.fv
  have dv_cache_0001 : Disjoint ((syn_cpw1 R)).fv ((syn_clnpairraisefn)).fv := by
    exact (show Disjoint ((syn_cpw1 R)).fv ((syn_clnpairraisefn)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn]; exact (show Disjoint ((R).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 :=
    (by simpa [syn_clnsifn] using (Nominal.classEqRefl (syn_clnsifn)))
  have p0001 :=
    @g_fveq1i (syn_csn R) (syn_clnsifn) (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) p0000
  have p0002 :=
    @g_fnfullfun (syn_cpw1fn)
  have p0003 :=
    @g_snex R
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cfullfun (syn_cpw1fn)) (syn_cvv)) (.classMem (syn_csn R) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fvco2 (syn_cvv) (syn_csn R) (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_fvfullfun (syn_csn R) (syn_cpw1fn)
  have p0008 :=
    @g_pw1fnval R hyp_lnsifnrawval_1
  have p0009 :=
    @g_eqtri (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn R)) (syn_cfv (syn_cpw1fn) (syn_csn R)) (syn_cpw1 R) p0007 p0008
  have p0010 :=
    @g_fveq2i (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn R)) (syn_cpw1 R) (syn_cimage (syn_clnpairraisefn)) p0009
  have p0011 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) (syn_csn R)) (syn_cfv (syn_cimage (syn_clnpairraisefn)) (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn R))) (syn_cfv (syn_cimage (syn_clnpairraisefn)) (syn_cpw1 R)) p0006 p0010
  have p0012 :=
    (by simpa [syn_clnpairraisefn] using (Nominal.classEqRefl (syn_clnpairraisefn)))
  have p0013 :=
    @g_n_1stex
  have p0014 :=
    @g_imageex (syn_c1st) p0013
  have p0015 :=
    @g_n_2ndex
  have p0016 :=
    @g_imageex (syn_c2nd) p0015
  have p0017 :=
    @g_txpex (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)) p0014 p0016
  have p0018 :=
    @g_eqeltri (syn_clnpairraisefn) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv) p0012 p0017
  have p0019 :=
    @g_pw1ex R hyp_lnsifnrawval_1
  have p0020 :=
    @g_wppfvimage (syn_cpw1 R) (syn_clnpairraisefn) dv_cache_0001 p0018 p0019
  have p0021 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) (syn_csn R)) (syn_cfv (syn_cimage (syn_clnpairraisefn)) (syn_cpw1 R)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) p0011 p0020
  have p0022 :=
    @g_eqtri (syn_cfv (syn_clnsifn) (syn_csn R)) (syn_cfv (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) (syn_csn R)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) p0001 p0021
  exact p0022

#print axioms g_lnsifnrawval

end NFChoice.DirectNominalPrf.WPPReplay
