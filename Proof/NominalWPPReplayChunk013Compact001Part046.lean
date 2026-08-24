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
import NominalWPPReplayChunk013Compact001Part045

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

noncomputable def g_df0c2
     :
    Nominal.NPrf (.classEq (syn_c0c) (syn_cnc (syn_c0))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_c0)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cen)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dfec2 x (syn_c0) (syn_cen) dv_cache_0001 dv_cache_0002
  have p0001 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc (syn_c0))))
  have p0002 :=
    @g_en0 (.cv x)
  have p0003 :=
    @g_ensym (syn_c0) (.cv x)
  have p0004 :=
    @g_el0c (.cv x)
  have p0005 :=
    @g_n_3bitr4ri (syn_wbr (.cv x) (syn_cen) (syn_c0)) (.classEq (.cv x) (syn_c0)) (syn_wbr (syn_c0) (syn_cen) (.cv x)) (.classMem (.cv x) (syn_c0c)) p0002 p0003 p0004
  have p0006 :=
    @g_eqabi (syn_wbr (syn_c0) (syn_cen) (.cv x)) x (syn_c0c) dv_cache_0003 p0005
  have p0007 :=
    @g_n_3eqtr4ri (syn_cec (syn_c0) (syn_cen)) (.cab x (syn_wbr (syn_c0) (syn_cen) (.cv x))) (syn_cnc (syn_c0)) (syn_c0c) p0000 p0001 p0006
  exact p0007

noncomputable def g_n_0cnc
     :
    Nominal.NPrf (.classMem (syn_c0c) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_df0c2
  have p0001 :=
    @g_n_0ex
  have p0002 :=
    @g_ncelncsi (syn_c0) p0001
  have p0003 :=
    @g_eqeltri (syn_c0c) (syn_cnc (syn_c0)) (syn_cncs) p0000 p0002
  exact p0003

noncomputable def g_n_1cnc
     :
    Nominal.NPrf (.classMem (syn_c1c) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let f : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
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
  have fresh_x_ne_f : x ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_f : y ≠ f := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_z_ne_f : z ≠ f := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_f_ne_z : f ≠ z :=
    Ne.symm fresh_z_ne_f
  have dv_cache_0001 : z ∉ ((syn_csn (.cv y))).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cen)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_csn (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : f ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cfv (.cv f) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classEq (.cv z) (syn_csn (syn_cfv (.cv f) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_y, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : f ∉ ((syn_wex x (.classEq (.cv z) (syn_csn (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_z, fresh_f_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_csn (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.classEq (syn_c1c) (syn_cnc (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dfec2 z (syn_csn (.cv y)) (syn_cen) dv_cache_0001 dv_cache_0002
  have p0001 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc (syn_csn (.cv y)))))
  have p0002 :=
    @g_el1c x (.cv z) dv_cache_0003
  have p0003 :=
    @g_vex y
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_en2sn (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (syn_wbr (syn_csn (.cv y)) (syn_cen) (syn_csn (.cv x))) p0003 p0004 p0005
  have p0007 :=
    @g_breq2 (.cv z) (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_cen)
  have p0008 :=
    @g_mpbiri (.classEq (.cv z) (syn_csn (.cv x))) (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) (syn_wbr (syn_csn (.cv y)) (syn_cen) (syn_csn (.cv x))) p0006 p0007
  have p0009 :=
    @g_exlimiv (.classEq (.cv z) (syn_csn (.cv x))) (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) x dv_cache_0004 p0008
  have p0010 :=
    @g_bren (syn_csn (.cv y)) (.cv z) f dv_cache_0005 dv_cache_0006
  have p0011 :=
    @g_f1of (syn_csn (.cv y)) (.cv z) (.cv f)
  have p0012 :=
    @g_f1ofo (syn_csn (.cv y)) (.cv z) (.cv f)
  have p0013 :=
    @g_forn (syn_csn (.cv y)) (.cv z) (.cv f)
  have p0014 :=
    @g_syl (syn_wf1o (.cv f) (syn_csn (.cv y)) (.cv z)) (syn_wfo (.cv f) (syn_csn (.cv y)) (.cv z)) (.classEq (syn_crn (.cv f)) (.cv z)) p0012 p0013
  have p0015 :=
    @g_fsn2 (.cv y) (.cv z) (.cv f) p0003
  have p0016 :=
    @g_rneq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y))))
  have p0017 :=
    @g_rnsnop (.cv y) (syn_cfv (.cv f) (.cv y)) p0003
  have p0018 :=
    @g_syl6eq (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y))))) (syn_crn (.cv f)) (syn_crn (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y))))) (syn_csn (syn_cfv (.cv f) (.cv y))) p0016 p0017
  have p0019 :=
    @g_eqeq1d (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y))))) (syn_crn (.cv f)) (syn_csn (syn_cfv (.cv f) (.cv y))) (.cv z) p0018
  have p0020 :=
    @g_fvex (.cv y) (.cv f)
  have p0021 :=
    @g_sneq (.cv x) (syn_cfv (.cv f) (.cv y))
  have p0022 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cfv (.cv f) (.cv y))) (syn_csn (.cv x)) (syn_csn (syn_cfv (.cv f) (.cv y))) (.cv z) p0021
  have p0023 :=
    @g_spcev (.classEq (.cv z) (syn_csn (.cv x))) (.classEq (.cv z) (syn_csn (syn_cfv (.cv f) (.cv y)))) x (syn_cfv (.cv f) (.cv y)) dv_cache_0007 dv_cache_0008 p0020 p0022
  have p0024 :=
    @g_eqcoms (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) (.cv z) (syn_csn (syn_cfv (.cv f) (.cv y))) p0023
  have p0025 :=
    @g_syl6bi (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y))))) (.classEq (syn_crn (.cv f)) (.cv z)) (.classEq (syn_csn (syn_cfv (.cv f) (.cv y))) (.cv z)) (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) p0019 p0024
  have p0026 :=
    @g_adantl (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y))))) (.imp (.classEq (syn_crn (.cv f)) (.cv z)) (syn_wex x (.classEq (.cv z) (syn_csn (.cv x))))) (.classMem (syn_cfv (.cv f) (.cv y)) (.cv z)) p0025
  have p0027 :=
    @g_sylbi (syn_wf (.cv f) (syn_csn (.cv y)) (.cv z)) (syn_wa (.classMem (syn_cfv (.cv f) (.cv y)) (.cv z)) (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y)))))) (.imp (.classEq (syn_crn (.cv f)) (.cv z)) (syn_wex x (.classEq (.cv z) (syn_csn (.cv x))))) p0015 p0026
  have p0028 :=
    @g_sylc (syn_wf1o (.cv f) (syn_csn (.cv y)) (.cv z)) (syn_wf (.cv f) (syn_csn (.cv y)) (.cv z)) (.classEq (syn_crn (.cv f)) (.cv z)) (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) p0011 p0014 p0027
  have p0029 :=
    @g_exlimiv (syn_wf1o (.cv f) (syn_csn (.cv y)) (.cv z)) (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) f dv_cache_0009 p0028
  have p0030 :=
    @g_sylbi (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) (syn_wex f (syn_wf1o (.cv f) (syn_csn (.cv y)) (.cv z))) (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) p0010 p0029
  have p0031 :=
    @g_impbii (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) p0009 p0030
  have p0032 :=
    @g_bitri (.classMem (.cv z) (syn_c1c)) (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) p0002 p0031
  have p0033 :=
    @g_eqabi (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) z (syn_c1c) dv_cache_0010 p0032
  have p0034 :=
    @g_n_3eqtr4ri (syn_cec (syn_csn (.cv y)) (syn_cen)) (.cab z (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z))) (syn_cnc (syn_csn (.cv y))) (syn_c1c) p0000 p0001 p0033
  have p0035 :=
    @g_snex (.cv y)
  have p0036 :=
    @g_nceq (.cv x) (syn_csn (.cv y))
  have p0037 :=
    @g_eqeq2d (.classEq (.cv x) (syn_csn (.cv y))) (syn_cnc (.cv x)) (syn_cnc (syn_csn (.cv y))) (syn_c1c) p0036
  have p0038 :=
    @g_spcev (.classEq (syn_c1c) (syn_cnc (.cv x))) (.classEq (syn_c1c) (syn_cnc (syn_csn (.cv y)))) x (syn_csn (.cv y)) dv_cache_0011 dv_cache_0012 p0035 p0037
  have p0039 :=
    Nominal.mp p0034 p0038
  have p0040 :=
    @g_elncs x (syn_c1c) dv_cache_0013
  have p0041 :=
    @g_mpbir (.classMem (syn_c1c) (syn_cncs)) (syn_wex x (.classEq (syn_c1c) (syn_cnc (.cv x)))) p0039 p0040
  exact p0041

noncomputable def g_df1c3
    (A : Class) (hyp_df1c3_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_c1c) (syn_cnc (syn_csn A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_snel1c A hyp_df1c3_1
  have p0001 :=
    @g_n_1cnc
  have p0002 :=
    @g_ncseqnc (syn_c1c) (syn_csn A)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_mpbir (.classEq (syn_c1c) (syn_cnc (syn_csn A))) (.classMem (syn_csn A) (syn_c1c)) p0000 p0003
  exact p0004

noncomputable def g_ncaddccl
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.classMem (syn_cplc A B) (syn_cncs))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Wff.classEq (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cnc (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (syn_cplc A B) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classMem (syn_cplc A B) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs x A dv_cache_0001
  have p0001 :=
    @g_elncs y B dv_cache_0002
  have p0002 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y dv_cache_0003 dv_cache_0004
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_n_0ex
  have p0005 :=
    @g_complex (syn_c0) p0004
  have p0006 :=
    @g_xpsnen (.cv x) (syn_ccompl (syn_c0)) p0003 p0005
  have p0007 :=
    @g_snex (syn_ccompl (syn_c0))
  have p0008 :=
    @g_xpex (.cv x) (syn_csn (syn_ccompl (syn_c0))) p0003 p0007
  have p0009 :=
    @g_eqnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (.cv x) p0008
  have p0010 :=
    @g_mpbir (.classEq (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (.cv x))) (syn_wbr (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cen) (.cv x)) p0006 p0009
  have p0011 :=
    @g_eqcomi (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (.cv x)) p0010
  have p0012 :=
    @g_eqtr A (syn_cnc (.cv x)) (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
  have p0013 :=
    @g_mpan2 (.classEq A (syn_cnc (.cv x))) (.classEq (syn_cnc (.cv x)) (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) p0011 p0012
  have p0014 :=
    @g_vex y
  have p0015 :=
    @g_n_0ex
  have p0016 :=
    @g_xpsnen (.cv y) (syn_c0) p0014 p0015
  have p0017 :=
    @g_snex (syn_c0)
  have p0018 :=
    @g_xpex (.cv y) (syn_csn (syn_c0)) p0014 p0017
  have p0019 :=
    @g_eqnc (syn_cxp (.cv y) (syn_csn (syn_c0))) (.cv y) p0018
  have p0020 :=
    @g_mpbir (.classEq (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cnc (.cv y))) (syn_wbr (syn_cxp (.cv y) (syn_csn (syn_c0))) (syn_cen) (.cv y)) p0016 p0019
  have p0021 :=
    @g_eqcomi (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cnc (.cv y)) p0020
  have p0022 :=
    @g_eqtr B (syn_cnc (.cv y)) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0023 :=
    @g_mpan2 (.classEq B (syn_cnc (.cv y))) (.classEq (syn_cnc (.cv y)) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) p0021 p0022
  have p0024 :=
    @g_addceq12 A B (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0025 :=
    @g_necompl (syn_c0)
  have p0026 :=
    @g_xpnedisj (.cv x) (.cv y) (syn_ccompl (syn_c0)) (syn_c0) p0005 p0025
  have p0027 :=
    @g_ncdisjun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))) p0008 p0018
  have p0028 :=
    Nominal.mp p0026 p0027
  have p0029 :=
    @g_eqcomi (syn_cnc (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) p0028
  have p0030 :=
    @g_unex (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))) p0008 p0018
  have p0031 :=
    @g_nceq (.cv z) (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0032 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cnc (.cv z)) (syn_cnc (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) p0031
  have p0033 :=
    @g_spcev (.classEq (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cnc (.cv z))) (.classEq (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cnc (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))))) z (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cxp (.cv y) (syn_csn (syn_c0)))) dv_cache_0005 dv_cache_0006 p0030 p0032
  have p0034 :=
    Nominal.mp p0029 p0033
  have p0035 :=
    @g_elncs z (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) dv_cache_0007
  have p0036 :=
    @g_mpbir (.classMem (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cncs)) (syn_wex z (.classEq (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cnc (.cv z)))) p0034 p0035
  have p0037 :=
    @g_syl6eqel (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cplc A B) (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cncs) p0024 p0036
  have p0038 :=
    @g_syl2an (.classEq A (syn_cnc (.cv x))) (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (.classMem (syn_cplc A B) (syn_cncs)) (.classEq B (syn_cnc (.cv y))) p0013 p0023 p0037
  have p0039 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) (.classMem (syn_cplc A B) (syn_cncs)) x y dv_cache_0008 dv_cache_0009 p0038
  have p0040 :=
    @g_sylbir (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x)))) (syn_wex y (.classEq B (syn_cnc (.cv y))))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))))) (.classMem (syn_cplc A B) (syn_cncs)) p0002 p0039
  have p0041 :=
    @g_syl2anb (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x)))) (syn_wex y (.classEq B (syn_cnc (.cv y)))) (.classMem (syn_cplc A B) (syn_cncs)) (.classMem B (syn_cncs)) p0000 p0001 p0040
  exact p0041

noncomputable def g_peano2nc
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cncs)) (.classMem (syn_cplc A (syn_c1c)) (syn_cncs))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_n_1cnc
  have p0001 :=
    @g_ncaddccl A (syn_c1c)
  have p0002 :=
    @g_mpan2 (.classMem A (syn_cncs)) (.classMem (syn_c1c) (syn_cncs)) (.classMem (syn_cplc A (syn_c1c)) (syn_cncs)) p0000 p0001
  exact p0002

noncomputable def g_nnnc
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (.classMem A (syn_cncs))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x_ne_n : x ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have dv_cache_0001 : x ∉ ((syn_cncs)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (.cv n) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((Wff.classMem (.cv x) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_c0c) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classMem A (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ n from (by exact fresh_x_ne_n))
  have p0000 :=
    @g_abid2 x (syn_cncs) dv_cache_0001
  have p0001 :=
    @g_ncsex
  have p0002 :=
    @g_eqeltri (.cab x (.classMem (.cv x) (syn_cncs))) (syn_cncs) (syn_cvv) p0000 p0001
  have p0003 :=
    @g_eleq1 (.cv x) (syn_c0c) (syn_cncs)
  have p0004 :=
    @g_eleq1 (.cv x) (.cv n) (syn_cncs)
  have p0005 :=
    @g_eleq1 (.cv x) (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)
  have p0006 :=
    @g_eleq1 (.cv x) A (syn_cncs)
  have p0007 :=
    @g_n_0cnc
  have p0008 :=
    @g_peano2nc (.cv n)
  have p0009 :=
    @g_a1i (.imp (.classMem (.cv n) (syn_cncs)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) p0008
  have p0010_e02_recanon : Nominal.NPrf (.imp (.objEq x n) (syn_wb (.classMem (.cv x) (syn_cncs)) (.classMem (.cv n) (syn_cncs)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cncs syn_cqs syn_wrex syn_wex syn_wa syn_cec syn_cima syn_csn syn_cvv syn_cen syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0010 :=
    @g_finds (.classMem (.cv x) (syn_cncs)) (.classMem (syn_c0c) (syn_cncs)) (.classMem (.cv n) (syn_cncs)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)) (.classMem A (syn_cncs)) x n A dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0002 p0003 p0010_e02_recanon p0005 p0006 p0007 p0009
  exact p0010

noncomputable def g_ncdisjeq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
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
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs x A dv_cache_0001
  have p0001 :=
    @g_elncs y B dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x)))) (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x)))) (syn_wex y (.classEq B (syn_cnc (.cv y))))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))))) p0002 p0003
  have p0005 :=
    @g_ener
  have p0006 :=
    @g_erdisj (.cv x) (.cv y) (syn_cen)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc (.cv x))))
  have p0009 :=
    @g_eqtr A (syn_cnc (.cv x)) (syn_cec (.cv x) (syn_cen))
  have p0010 :=
    @g_mpan2 (.classEq A (syn_cnc (.cv x))) (.classEq (syn_cnc (.cv x)) (syn_cec (.cv x) (syn_cen))) (.classEq A (syn_cec (.cv x) (syn_cen))) p0008 p0009
  have p0011 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc (.cv y))))
  have p0012 :=
    @g_eqtr B (syn_cnc (.cv y)) (syn_cec (.cv y) (syn_cen))
  have p0013 :=
    @g_mpan2 (.classEq B (syn_cnc (.cv y))) (.classEq (syn_cnc (.cv y)) (syn_cec (.cv y) (syn_cen))) (.classEq B (syn_cec (.cv y) (syn_cen))) p0011 p0012
  have p0014 :=
    @g_eqeq12 A (syn_cec (.cv x) (syn_cen)) B (syn_cec (.cv y) (syn_cen))
  have p0015 :=
    @g_ineq12 A (syn_cec (.cv x) (syn_cen)) B (syn_cec (.cv y) (syn_cen))
  have p0016 :=
    @g_eqeq1d (syn_wa (.classEq A (syn_cec (.cv x) (syn_cen))) (.classEq B (syn_cec (.cv y) (syn_cen)))) (syn_cin A B) (syn_cin (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen))) (syn_c0) p0015
  have p0017 :=
    @g_orbi12d (syn_wa (.classEq A (syn_cec (.cv x) (syn_cen))) (.classEq B (syn_cec (.cv y) (syn_cen)))) (.classEq A B) (.classEq (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen))) (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cin (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen))) (syn_c0)) p0014 p0016
  have p0018 :=
    @g_syl2an (.classEq A (syn_cnc (.cv x))) (.classEq A (syn_cec (.cv x) (syn_cen))) (.classEq B (syn_cec (.cv y) (syn_cen))) (syn_wb (syn_wo (.classEq A B) (.classEq (syn_cin A B) (syn_c0))) (syn_wo (.classEq (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen))) (.classEq (syn_cin (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen))) (syn_c0)))) (.classEq B (syn_cnc (.cv y))) p0010 p0013 p0017
  have p0019 :=
    @g_mpbiri (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) (syn_wo (.classEq A B) (.classEq (syn_cin A B) (syn_c0))) (syn_wo (.classEq (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen))) (.classEq (syn_cin (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen))) (syn_c0))) p0007 p0018
  have p0020 :=
    @g_orcomd (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) (.classEq A B) (.classEq (syn_cin A B) (syn_c0)) p0019
  have p0021 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) (syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B)) x y dv_cache_0005 dv_cache_0006 p0020
  have p0022 :=
    @g_sylbi (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))))) (syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B)) p0004 p0021
  exact p0022

noncomputable def g_nceleq
    (A : Class) (B : Class) (X : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (.classMem X A) (.classMem X B))) (.classEq A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ X.fv
  have p0000 :=
    @g_elin X A B
  have p0001 :=
    @g_n0i (syn_cin A B) X
  have p0002 :=
    @g_sylbir (syn_wa (.classMem X A) (.classMem X B)) (.classMem X (syn_cin A B)) (.neg (.classEq (syn_cin A B) (syn_c0))) p0000 p0001
  have p0003 :=
    @g_ncdisjeq A B
  have p0004 :=
    @g_ord (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.classEq (syn_cin A B) (syn_c0)) (.classEq A B) p0003
  have p0005 :=
    @g_syl5 (syn_wa (.classMem X A) (.classMem X B)) (.neg (.classEq (syn_cin A B) (syn_c0))) (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.classEq A B) p0002 p0004
  have p0006 :=
    @g_imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wa (.classMem X A) (.classMem X B)) (.classEq A B) p0005
  exact p0006

noncomputable def g_ncpw1
    (A : Class) (B : Class) (hyp_ncpw1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classEq (syn_cnc A) (syn_cnc B)) (.classEq (syn_cnc (syn_cpw1 A)) (syn_cnc (syn_cpw1 B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_enpw1 A B
  have p0001 :=
    @g_eqnc A B hyp_ncpw1_1
  have p0002 :=
    @g_pw1ex A hyp_ncpw1_1
  have p0003 :=
    @g_eqnc (syn_cpw1 A) (syn_cpw1 B) p0002
  have p0004 :=
    @g_n_3bitr4i (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B)) (.classEq (syn_cnc A) (syn_cnc B)) (.classEq (syn_cnc (syn_cpw1 A)) (syn_cnc (syn_cpw1 B))) p0000 p0001 p0003
  exact p0004

noncomputable def g_ncpwpw1
    (A : Class) (hyp_ncpwpw1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cnc (syn_cpw (syn_cpw1 A))) (syn_cnc (syn_cpw1 (syn_cpw A)))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_enpw1pw A hyp_ncpwpw1_1
  have p0001 :=
    @g_ensym (syn_cpw1 (syn_cpw A)) (syn_cpw (syn_cpw1 A))
  have p0002 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw A)) (syn_cen) (syn_cpw (syn_cpw1 A))) (syn_wbr (syn_cpw (syn_cpw1 A)) (syn_cen) (syn_cpw1 (syn_cpw A))) p0000 p0001
  have p0003 :=
    @g_pw1ex A hyp_ncpwpw1_1
  have p0004 :=
    @g_pwex (syn_cpw1 A) p0003
  have p0005 :=
    @g_eqnc (syn_cpw (syn_cpw1 A)) (syn_cpw1 (syn_cpw A)) p0004
  have p0006 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw (syn_cpw1 A))) (syn_cnc (syn_cpw1 (syn_cpw A)))) (syn_wbr (syn_cpw (syn_cpw1 A)) (syn_cen) (syn_cpw1 (syn_cpw A))) p0002 p0005
  exact p0006

noncomputable def g_ncpw1c
     :
    Nominal.NPrf (.classEq (syn_cnc (syn_cpw (syn_c1c))) (syn_cnc (syn_c1c))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_vvex
  have p0001 :=
    @g_ncpwpw1 (syn_cvv) p0000
  have p0002 :=
    @g_df1c2
  have p0003 :=
    @g_pweqi (syn_c1c) (syn_cpw1 (syn_cvv)) p0002
  have p0004 :=
    @g_nceqi (syn_cpw (syn_c1c)) (syn_cpw (syn_cpw1 (syn_cvv))) p0003
  have p0005 :=
    @g_df1c2
  have p0006 :=
    @g_pwv
  have p0007 :=
    @g_pw1eq (syn_cpw (syn_cvv)) (syn_cvv)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_eqtr4i (syn_c1c) (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cpw (syn_cvv))) p0005 p0008
  have p0010 :=
    @g_nceqi (syn_c1c) (syn_cpw1 (syn_cpw (syn_cvv))) p0009
  have p0011 :=
    @g_n_3eqtr4i (syn_cnc (syn_cpw (syn_cpw1 (syn_cvv)))) (syn_cnc (syn_cpw1 (syn_cpw (syn_cvv)))) (syn_cnc (syn_cpw (syn_c1c))) (syn_cnc (syn_c1c)) p0001 p0004 p0010
  exact p0011

noncomputable def g_n_1p1e2c
     :
    Nominal.NPrf (.classEq (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_0ex
  have p0001 :=
    @g_n0i (syn_cvv) (syn_c0)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_elsnc (syn_cvv) (syn_c0) p0003
  have p0005 :=
    @g_mtbir (.classMem (syn_cvv) (syn_csn (syn_c0))) (.classEq (syn_cvv) (syn_c0)) p0002 p0004
  have p0006 :=
    @g_disjsn (syn_csn (syn_c0)) (syn_cvv)
  have p0007 :=
    @g_mpbir (.classEq (syn_cin (syn_csn (syn_c0)) (syn_csn (syn_cvv))) (syn_c0)) (.neg (.classMem (syn_cvv) (syn_csn (syn_c0)))) p0005 p0006
  have p0008 :=
    @g_snex (syn_c0)
  have p0009 :=
    @g_snex (syn_cvv)
  have p0010 :=
    @g_ncdisjun (syn_csn (syn_c0)) (syn_csn (syn_cvv)) p0008 p0009
  have p0011 :=
    Nominal.mp p0007 p0010
  have p0012 :=
    (by simpa [syn_c2c] using (Nominal.classEqRefl (syn_c2c)))
  have p0013 :=
    (by simpa [syn_cpr] using (Nominal.classEqRefl (syn_cpr (syn_c0) (syn_cvv))))
  have p0014 :=
    @g_nceqi (syn_cpr (syn_c0) (syn_cvv)) (syn_cun (syn_csn (syn_c0)) (syn_csn (syn_cvv))) p0013
  have p0015 :=
    @g_eqtri (syn_c2c) (syn_cnc (syn_cpr (syn_c0) (syn_cvv))) (syn_cnc (syn_cun (syn_csn (syn_c0)) (syn_csn (syn_cvv)))) p0012 p0014
  have p0016 :=
    @g_n_0ex
  have p0017 :=
    @g_df1c3 (syn_c0) p0016
  have p0018 :=
    @g_vvex
  have p0019 :=
    @g_df1c3 (syn_cvv) p0018
  have p0020 :=
    @g_addceq12i (syn_c1c) (syn_cnc (syn_csn (syn_c0))) (syn_c1c) (syn_cnc (syn_csn (syn_cvv))) p0017 p0019
  have p0021 :=
    @g_n_3eqtr4ri (syn_cnc (syn_cun (syn_csn (syn_c0)) (syn_csn (syn_cvv)))) (syn_cplc (syn_cnc (syn_csn (syn_c0))) (syn_cnc (syn_csn (syn_cvv)))) (syn_c2c) (syn_cplc (syn_c1c) (syn_c1c)) p0011 p0015 p0020
  exact p0021

noncomputable def g_tcex
    (A : Class) :
    Nominal.NPrf (.classMem (syn_ctc A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
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
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc y A x dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_iotaex (syn_wa (.classMem (.cv x) (syn_cncs)) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) x
  have p0002 :=
    @g_eqeltri (syn_ctc A) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs)) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) (syn_cvv) p0000 p0001
  exact p0002

#print axioms g_tcex

end NFChoice.DirectNominalPrf.WPPReplay
