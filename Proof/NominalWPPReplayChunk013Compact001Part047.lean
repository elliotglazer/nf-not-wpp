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
import NominalWPPReplayChunk013Compact001Part046

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

noncomputable def g_tceq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ctc A) (syn_ctc B))) := by
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
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_rexeq (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) y A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_anbi2d (.classEq A B) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) (syn_wrex y B (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) (.classMem (.cv x) (syn_cncs)) p0000
  have p0002 :=
    @g_iotabidv (.classEq A B) (syn_wa (.classMem (.cv x) (syn_cncs)) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) (syn_wa (.classMem (.cv x) (syn_cncs)) (syn_wrex y B (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) x dv_cache_0003 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc y A x dv_cache_0004 dv_cache_0001 dv_cache_0005
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc y B x dv_cache_0006 dv_cache_0002 dv_cache_0005
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs)) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs)) (syn_wrex y B (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) (syn_ctc A) (syn_ctc B) p0002 p0003 p0004
  exact p0005

noncomputable def g_ncspw1eu
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.classMem A (syn_cncs)) (syn_wreu x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cnc (syn_cpw1 (.cv y)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.classMem A (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0009 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((Wff.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Wff.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0013 : y ∉ ((Wff.objEq x z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((Wff.objEq x z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_wa (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, (Ne.symm dv_x_y), fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : w ∉ ((syn_wa (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_x, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((Wff.classMem A (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((Wff.classMem A (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0021 : w ∉ ((Wff.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : z ∉ ((syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nulnnc
  have p0001 :=
    @g_eleq1 A (syn_c0) (syn_cncs)
  have p0002 :=
    @g_mtbiri (.classEq A (syn_c0)) (.classMem A (syn_cncs)) (.classMem (syn_c0) (syn_cncs)) p0000 p0001
  have p0003 :=
    @g_necon2ai (.classMem A (syn_cncs)) A (syn_c0) p0002
  have p0004 :=
    @g_n0 y A dv_cache_0001
  have p0005 :=
    @g_sylib (.classMem A (syn_cncs)) (syn_wne A (syn_c0)) (syn_wex y (.classMem (.cv y) A)) p0003 p0004
  have p0006 :=
    @g_vex y
  have p0007 :=
    @g_pw1ex (.cv y) p0006
  have p0008 :=
    @g_ncelncsi (syn_cpw1 (.cv y)) p0007
  have p0009 :=
    @g_eqid (syn_cnc (syn_cpw1 (.cv y)))
  have p0010 :=
    @g_eqeq1 (.cv x) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv y)))
  have p0011 :=
    @g_rspcev (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv y)))) x (syn_cnc (syn_cpw1 (.cv y))) (syn_cncs) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0010
  have p0012 :=
    @g_mp2an (.classMem (syn_cnc (syn_cpw1 (.cv y))) (syn_cncs)) (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv y)))) (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) p0008 p0009 p0011
  have p0013 :=
    @g_jctr (.classMem (.cv y) A) (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) p0012
  have p0014 :=
    @g_a1i (.imp (.classMem (.cv y) A) (syn_wa (.classMem (.cv y) A) (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) (.classMem A (syn_cncs)) p0013
  have p0015 :=
    @g_eximdv (.classMem A (syn_cncs)) (.classMem (.cv y) A) (syn_wa (.classMem (.cv y) A) (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) y dv_cache_0005 p0014
  have p0016 :=
    @g_mpd (.classMem A (syn_cncs)) (syn_wex y (.classMem (.cv y) A)) (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) p0005 p0015
  have p0017 :=
    @g_rexcom (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) x y (syn_cncs) A dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0018 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y A (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))))
  have p0019 :=
    @g_bitri (syn_wrex x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) (syn_wrex y A (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) p0017 p0018
  have p0020 :=
    @g_sylibr (.classMem A (syn_cncs)) (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) (syn_wrex x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) p0016 p0019
  have p0021 :=
    @g_reeanv (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))) y w A A dv_cache_0009 dv_cache_0001 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0022 :=
    @g_ncseqnc A (.cv y)
  have p0023 :=
    @g_biimpar (.classMem A (syn_cncs)) (.classEq A (syn_cnc (.cv y))) (.classMem (.cv y) A) p0022
  have p0024 :=
    @g_adantrr (.classMem A (syn_cncs)) (.classMem (.cv y) A) (.classEq A (syn_cnc (.cv y))) (.classMem (.cv w) A) p0023
  have p0025 :=
    @g_ncseqnc A (.cv w)
  have p0026 :=
    @g_biimpar (.classMem A (syn_cncs)) (.classEq A (syn_cnc (.cv w))) (.classMem (.cv w) A) p0025
  have p0027 :=
    @g_adantrl (.classMem A (syn_cncs)) (.classMem (.cv w) A) (.classEq A (syn_cnc (.cv w))) (.classMem (.cv y) A) p0026
  have p0028 :=
    @g_eqtr3d (syn_wa (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A))) A (syn_cnc (.cv y)) (syn_cnc (.cv w)) p0024 p0027
  have p0029 :=
    @g_ncpw1 (.cv y) (.cv w) p0006
  have p0030 :=
    @g_sylib (syn_wa (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A))) (.classEq (syn_cnc (.cv y)) (syn_cnc (.cv w))) (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w)))) p0028 p0029
  have p0031 :=
    @g_n_3adant2 (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A)) (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w)))) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))) p0030
  have p0032 :=
    @g_eqeq2 (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w))) (.cv x)
  have p0033 :=
    @g_anbi1d (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w)))) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv w)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))) p0032
  have p0034 :=
    @g_eqtr3 (.cv x) (.cv z) (syn_cnc (syn_cpw1 (.cv w)))
  have p0035_e01_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv w)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnc syn_cec syn_cima syn_wrex syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cen syn_copab syn_cpw1 syn_cin syn_cpw syn_wss syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0034
  have p0035 :=
    @g_syl6bi (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w)))) (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv w)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) (.objEq x z) p0033 p0035_e01_recanon
  have p0036 :=
    @g_syl (syn_w3a (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A))) (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w)))) (.imp (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) (.objEq x z)) p0031 p0035
  have p0037 :=
    @g_n_3expa (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A)) (.imp (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) (.objEq x z)) p0036
  have p0038 :=
    @g_rexlimdvva (syn_wa (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs)))) (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) (.objEq x z) y w A A dv_cache_0009 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0012 p0037
  have p0039 :=
    @g_syl5bir (syn_wa (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))) (syn_wrex y A (syn_wrex w A (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))))) (syn_wa (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs)))) (.objEq x z) p0021 p0038
  have p0040 :=
    @g_ralrimivva (.classMem A (syn_cncs)) (.imp (syn_wa (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))) (.objEq x z)) x z (syn_cncs) (syn_cncs) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0039
  have p0041 :=
    @g_eqeq1 (.cv x) (.cv z) (syn_cnc (syn_cpw1 (.cv y)))
  have p0042_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (syn_wb (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cnc syn_cec syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cen syn_copab syn_cpw1 syn_cin syn_cpw syn_wss syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0041
  have p0042 :=
    @g_rexbidv (.objEq x z) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y)))) y A dv_cache_0013 p0042_e00_recanon
  have p0043 :=
    @g_pw1eq (.cv y) (.cv w)
  have p0044_e00_recanon : Nominal.NPrf (.imp (.objEq y w) (.classEq (syn_cpw1 (.cv y)) (syn_cpw1 (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0043
  have p0044 :=
    @g_nceqd (.objEq y w) (syn_cpw1 (.cv y)) (syn_cpw1 (.cv w)) p0044_e00_recanon
  have p0045 :=
    @g_eqeq2d (.objEq y w) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w))) (.cv z) p0044
  have p0046 :=
    @g_cbvrexv (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))) y w A dv_cache_0001 dv_cache_0009 dv_cache_0021 dv_cache_0011 p0045
  have p0047 :=
    @g_syl6bb (.objEq x z) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) (syn_wrex y A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y))))) (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) p0042 p0046
  have p0048 :=
    @g_reu4 (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) x z (syn_cncs) dv_cache_0003 dv_cache_0017 dv_cache_0022 dv_cache_0023 dv_cache_0020 p0047
  have p0049 :=
    @g_sylanbrc (.classMem A (syn_cncs)) (syn_wrex x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) (syn_wral x (syn_cncs) (syn_wral z (syn_cncs) (.imp (syn_wa (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))) (.objEq x z)))) (syn_wreu x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) p0020 p0040 p0048
  exact p0049

noncomputable def g_tccl
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cncs)) (.classMem (syn_ctc A) (syn_cncs))) := by
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
  have dv_cache_0004 : x ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc y A x dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_ncspw1eu x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_reiotacl (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) x (syn_cncs) dv_cache_0004
  have p0003 :=
    @g_syl (.classMem A (syn_cncs)) (syn_wreu x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))) (.classMem (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs)) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) (syn_cncs)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A (syn_cncs)) (syn_ctc A) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs)) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) (syn_cncs) p0000 p0003
  exact p0004

noncomputable def g_eqtc
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (.classMem A (syn_cncs)) (syn_wb (.classEq (syn_ctc A) B) (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classMem B (syn_cncs))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cncs)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem A (syn_cncs)) (.classEq (syn_ctc A) B)
  have p0001 :=
    @g_tccl A
  have p0002 :=
    @g_adantr (.classMem A (syn_cncs)) (.classMem (syn_ctc A) (syn_cncs)) (.classEq (syn_ctc A) B) p0001
  have p0003 :=
    @g_eqeltrrd (syn_wa (.classMem A (syn_cncs)) (.classEq (syn_ctc A) B)) (syn_ctc A) B (syn_cncs) p0000 p0002
  have p0004 :=
    @g_ex (.classMem A (syn_cncs)) (.classEq (syn_ctc A) B) (.classMem B (syn_cncs)) p0003
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_pw1ex (.cv x) p0005
  have p0007 :=
    @g_ncelncsi (syn_cpw1 (.cv x)) p0006
  have p0008 :=
    @g_eleq1 B (syn_cnc (syn_cpw1 (.cv x))) (syn_cncs)
  have p0009 :=
    @g_mpbiri (.classEq B (syn_cnc (syn_cpw1 (.cv x)))) (.classMem B (syn_cncs)) (.classMem (syn_cnc (syn_cpw1 (.cv x))) (syn_cncs)) p0007 p0008
  have p0010 :=
    @g_rexlimivw (.classEq B (syn_cnc (syn_cpw1 (.cv x)))) (.classMem B (syn_cncs)) x A dv_cache_0001 p0009
  have p0011 :=
    @g_a1i (.imp (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) (.classMem B (syn_cncs))) (.classMem A (syn_cncs)) p0010
  have p0012 :=
    @g_ncspw1eu y x A dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0013 :=
    @g_eqeq1 (.cv y) B (syn_cnc (syn_cpw1 (.cv x)))
  have p0014 :=
    @g_rexbidv (.classEq (.cv y) B) (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x)))) (.classEq B (syn_cnc (syn_cpw1 (.cv x)))) x A dv_cache_0005 p0013
  have p0015 :=
    @g_reiota2 (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))) (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) y (syn_cncs) B dv_cache_0006 dv_cache_0007 dv_cache_0008 p0014
  have p0016 :=
    @g_sylan2 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (syn_wreu y (syn_cncs) (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x)))))) (syn_wb (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) (.classEq (syn_cio y (syn_wa (.classMem (.cv y) (syn_cncs)) (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))))) B)) p0012 p0015
  have p0017 :=
    @g_ancoms (.classMem B (syn_cncs)) (.classMem A (syn_cncs)) (syn_wb (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) (.classEq (syn_cio y (syn_wa (.classMem (.cv y) (syn_cncs)) (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))))) B)) p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc x A y dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0019 :=
    @g_eqeq1i (syn_ctc A) (syn_cio y (syn_wa (.classMem (.cv y) (syn_cncs)) (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))))) B p0018
  have p0020 :=
    @g_syl6rbbr (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) (.classEq (syn_cio y (syn_wa (.classMem (.cv y) (syn_cncs)) (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))))) B) (.classEq (syn_ctc A) B) p0017 p0019
  have p0021 :=
    @g_ex (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (syn_wb (.classEq (syn_ctc A) B) (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x)))))) p0020
  have p0022 :=
    @g_pm5_21ndd (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classEq (syn_ctc A) B) (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) p0004 p0011 p0021
  exact p0022

noncomputable def g_pw1eltc
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B A)) (.classMem (syn_cpw1 B) (syn_ctc A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 B)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cnc (syn_cpw1 B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pw1exg B A
  have p0001 :=
    @g_ncidg (syn_cpw1 B) (syn_cvv)
  have p0002 :=
    @g_syl (.classMem B A) (.classMem (syn_cpw1 B) (syn_cvv)) (.classMem (syn_cpw1 B) (syn_cnc (syn_cpw1 B))) p0000 p0001
  have p0003 :=
    @g_adantl (.classMem B A) (.classMem (syn_cpw1 B) (syn_cnc (syn_cpw1 B))) (.classMem A (syn_cncs)) p0002
  have p0004 :=
    @g_eqid (syn_cnc (syn_cpw1 B))
  have p0005 :=
    @g_pw1eq (.cv y) B
  have p0006 :=
    @g_nceqd (.classEq (.cv y) B) (syn_cpw1 (.cv y)) (syn_cpw1 B) p0005
  have p0007 :=
    @g_eqeq2d (.classEq (.cv y) B) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 B)) p0006
  have p0008 :=
    @g_rspcev (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y)))) (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 B))) y B A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0007
  have p0009 :=
    @g_mpan2 (.classMem B A) (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 B))) (syn_wrex y A (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y))))) p0004 p0008
  have p0010 :=
    @g_adantl (.classMem B A) (syn_wrex y A (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y))))) (.classMem A (syn_cncs)) p0009
  have p0011 :=
    @g_eqtc y A (syn_cnc (syn_cpw1 B)) dv_cache_0002 dv_cache_0004
  have p0012 :=
    @g_adantr (.classMem A (syn_cncs)) (syn_wb (.classEq (syn_ctc A) (syn_cnc (syn_cpw1 B))) (syn_wrex y A (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y)))))) (.classMem B A) p0011
  have p0013 :=
    @g_mpbird (syn_wa (.classMem A (syn_cncs)) (.classMem B A)) (.classEq (syn_ctc A) (syn_cnc (syn_cpw1 B))) (syn_wrex y A (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y))))) p0010 p0012
  have p0014 :=
    @g_eleqtrrd (syn_wa (.classMem A (syn_cncs)) (.classMem B A)) (syn_cpw1 B) (syn_cnc (syn_cpw1 B)) (syn_ctc A) p0003 p0013
  exact p0014

noncomputable def g_tc0c
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_c0c)) (syn_c0c)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_0cnc
  have p0001 :=
    @g_tccl (syn_c0c)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_n_0cnc
  have p0004 :=
    @g_pw10
  have p0005 :=
    @g_n_0cnc
  have p0006 :=
    @g_nulel0c
  have p0007 :=
    @g_pw1eltc (syn_c0c) (syn_c0)
  have p0008 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cncs)) (.classMem (syn_c0) (syn_c0c)) (.classMem (syn_cpw1 (syn_c0)) (syn_ctc (syn_c0c))) p0005 p0006 p0007
  have p0009 :=
    @g_eqeltrri (syn_cpw1 (syn_c0)) (syn_c0) (syn_ctc (syn_c0c)) p0004 p0008
  have p0010 :=
    @g_nulel0c
  have p0011 :=
    @g_nceleq (syn_ctc (syn_c0c)) (syn_c0c) (syn_c0)
  have p0012 :=
    @g_mp4an (.classMem (syn_ctc (syn_c0c)) (syn_cncs)) (.classMem (syn_c0c) (syn_cncs)) (.classMem (syn_c0) (syn_ctc (syn_c0c))) (.classMem (syn_c0) (syn_c0c)) (.classEq (syn_ctc (syn_c0c)) (syn_c0c)) p0002 p0003 p0009 p0010 p0011
  exact p0012

#print axioms g_tc0c

end NFChoice.DirectNominalPrf.WPPReplay
