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
import NominalWPPReplayChunk013Compact001Part005

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

noncomputable def g_brpprod
    (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) (B : Class) (R : Class) (S : Class) (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_w : w ∉ B.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_R_w : w ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_S_w : w ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cpprod R S) B) (syn_wex x (syn_wex y (syn_wex z (syn_wex w (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ({w} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ S.fv
  have dv_cache_0001 : z ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_ccom R (syn_c1st))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_ccom R (syn_c1st))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_ccom S (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((syn_ccom S (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show z ≠ w from (by exact Ne.symm dv_w_z))
  have dv_cache_0010 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, (Ne.symm dv_w_x), dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, (Ne.symm dv_w_y), dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_wbr (.cv x) R (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_y_z, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((Wff.classEq B (syn_cop (.cv z) (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, dv_x_z, (Ne.symm dv_w_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((Wff.classEq B (syn_cop (.cv z) (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, dv_y_z, (Ne.symm dv_w_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cpprod] using (Nominal.classEqRefl (syn_cpprod R S)))
  have p0001 :=
    @g_breqi A B (syn_cpprod R S) (syn_ctxp (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd))) p0000
  have p0002 :=
    @g_brtxp z w A B (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0003 :=
    @g_brco x A (.cv z) R (syn_c1st) dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0004 :=
    @g_anbi1i (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wex x (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z)))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) p0003
  have p0005 :=
    @g_n_19_41v (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) x dv_cache_0014
  have p0006 :=
    @g_an32 (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_br1st y A (.cv x) dv_cache_0015 dv_cache_0016 p0007
  have p0009 :=
    @g_anbi1i (syn_wbr A (syn_c1st) (.cv x)) (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y)))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) p0008
  have p0010 :=
    @g_n_19_41v (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) y dv_cache_0017
  have p0011 :=
    @g_breq1 A (syn_cop (.cv x) (.cv y)) (.cv w) (syn_ccom S (syn_c2nd))
  have p0012 :=
    @g_vex y
  have p0013 :=
    @g_brco2nd (.cv x) (.cv y) (.cv w) S p0007 p0012
  have p0014 :=
    @g_syl6bb (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w)) (syn_wbr (.cv y) S (.cv w)) p0011 p0013
  have p0015 :=
    @g_pm5_32i (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) (syn_wbr (.cv y) S (.cv w)) p0014
  have p0016 :=
    @g_exbii (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))) y p0015
  have p0017 :=
    @g_n_3bitr2i (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wa (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y)))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))) (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w)))) p0009 p0010 p0016
  have p0018 :=
    @g_anbi1i (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w)))) (syn_wbr (.cv x) R (.cv z)) p0017
  have p0019 :=
    @g_anass (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))
  have p0020 :=
    @g_an32 (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))
  have p0021 :=
    @g_bitr3i (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))) (syn_wa (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv z))) (syn_wbr (.cv y) S (.cv w))) (syn_wa (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))) (syn_wbr (.cv x) R (.cv z))) p0019 p0020
  have p0022 :=
    @g_exbii (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))) (syn_wa (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))) (syn_wbr (.cv x) R (.cv z))) y p0021
  have p0023 :=
    @g_n_19_41v (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))) (syn_wbr (.cv x) R (.cv z)) y dv_cache_0018
  have p0024 :=
    @g_bitr2i (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))) (syn_wex y (syn_wa (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))) (syn_wbr (.cv x) R (.cv z)))) (syn_wa (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w)))) (syn_wbr (.cv x) R (.cv z))) p0022 p0023
  have p0025 :=
    @g_n_3bitri (syn_wa (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wa (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wbr (.cv x) R (.cv z))) (syn_wa (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w)))) (syn_wbr (.cv x) R (.cv z))) (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))) p0006 p0018 p0024
  have p0026 :=
    @g_exbii (syn_wa (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))) x p0025
  have p0027 :=
    @g_n_3bitr2i (syn_wa (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wa (syn_wex x (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z)))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wex x (syn_wa (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z))) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))) p0004 p0005 p0026
  have p0028 :=
    @g_anbi2i (syn_wa (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))) (.classEq B (syn_cop (.cv z) (.cv w))) p0027
  have p0029 :=
    @g_n_3anass (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))
  have p0030 :=
    @g_n_3ancoma (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))
  have p0031 :=
    @g_n_3anass (.classEq B (syn_cop (.cv z) (.cv w))) (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))
  have p0032 :=
    @g_bitri (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))) (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w))) (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))) (syn_wa (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))) p0030 p0031
  have p0033 :=
    @g_n_2exbii (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))) (syn_wa (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))) x y p0032
  have p0034 :=
    @g_n_19_42vv (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))) x y dv_cache_0019 dv_cache_0020
  have p0035 :=
    @g_bitri (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))) (syn_wex x (syn_wex y (syn_wa (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))) (syn_wa (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))) p0033 p0034
  have p0036 :=
    @g_n_3bitr4i (syn_wa (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))) (syn_wa (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))) (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))) p0028 p0029 p0035
  have p0037 :=
    @g_n_2exbii (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))) z w p0036
  have p0038 :=
    @g_exrot4 (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))) z w x y
  have p0039 :=
    @g_bitri (syn_wex z (syn_wex w (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))))) (syn_wex z (syn_wex w (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))))) (syn_wex x (syn_wex y (syn_wex z (syn_wex w (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))))) p0037 p0038
  have p0040 :=
    @g_n_3bitri (syn_wbr A (syn_cpprod R S) B) (syn_wbr A (syn_ctxp (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd))) B) (syn_wex z (syn_wex w (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))))) (syn_wex x (syn_wex y (syn_wex z (syn_wex w (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))))) p0001 p0002 p0039
  exact p0040

#print axioms g_brpprod

end NFChoice.DirectNominalPrf.WPPReplay
