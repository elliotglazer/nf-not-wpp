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
import NominalWPPReplayChunk017Compact001Part007

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

noncomputable def g_hnsiquomappreexndv
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) (hyp_hnsiquomappreexndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  let w : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_w_ne_r : w ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_w : r ≠ w :=
    Ne.symm fresh_w_ne_r
  have dv_cache_0001 : w ∉ ((syn_cpw1 A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_chwcn (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_chnsicodemap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cpw1 (syn_chnord A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, fresh_x_ne_r, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_y, fresh_r_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : r ∉ ((syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_y, fresh_r_not_A, fresh_r_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_y, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((Wff.classMem (.cv y) (syn_chnord (syn_cpw1 A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
  have p0001 :=
    @g_id (.classMem (.cv y) (syn_chnord (syn_cpw1 A)))
  have p0002 :=
    @g_elex (.cv y) (syn_chnord (syn_cpw1 A))
  have p0003 :=
    @g_syl (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (.classMem (.cv y) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_elhnordclndv w (syn_cpw1 A) (.cv y) dv_cache_0001 dv_cache_0002
  have p0005 :=
    @g_syl (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (.classMem (.cv y) (syn_cvv)) (syn_wb (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wrex w (syn_chwcn (syn_cpw1 A)) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) p0003 p0004
  have p0006 :=
    @g_mpbid (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wrex w (syn_chwcn (syn_cpw1 A)) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))) p0000 p0005
  have p0007 :=
    @g_hnsicodemapfondv A
  have p0008 :=
    @g_a1i (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) p0007
  have p0009 :=
    @g_simpr (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))
  have p0010 :=
    @g_simpl (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))
  have p0011 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))) (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) p0009 p0010
  have p0012 :=
    @g_jca (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) p0008 p0011
  have p0013 :=
    @g_foelrn r (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (.cv w) (syn_chnsicodemap A) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0014 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (.cv w) (syn_chwcn (syn_cpw1 A)))) (syn_wrex r (syn_cpw1 (syn_chwcn A)) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))) p0012 p0013
  have p0015 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0016 :=
    @g_simpl (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0015 p0016
  have p0018 :=
    @g_pw1argclcl (syn_chwcn A) (.cv r)
  have p0019 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) p0017 p0018
  have p0020 :=
    @g_simpl (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0019 p0020
  have p0022 :=
    @g_hwnisoclasselhnordcl A (syn_cuni (.cv r)) hyp_hnsiquomappreexndv_1
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)) p0021 p0022
  have p0024 :=
    @g_snelpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)
  have p0025 :=
    @g_sylibr (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)) (.classMem (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_cpw1 (syn_chnord A))) p0023 p0024
  have p0026 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0027 :=
    @g_simpr (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))) p0026 p0027
  have p0029 :=
    @g_simpr (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))
  have p0030 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))) p0028 p0029
  have p0031 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0032 :=
    @g_simpr (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))) p0031 p0032
  have p0034 :=
    @g_eceq1 (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))
  have p0035 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))) (.classEq (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A)))) p0033 p0034
  have p0036 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))) p0030 p0035
  have p0037 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0038 :=
    @g_simpl (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0039 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0037 p0038
  have p0040 :=
    @g_pw1argclcl (syn_chwcn A) (.cv r)
  have p0041 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) p0039 p0040
  have p0042 :=
    @g_simpl (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0041 p0042
  have p0044 :=
    @g_hwnisoclasselhnordcl A (syn_cuni (.cv r)) hyp_hnsiquomappreexndv_1
  have p0045 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)) p0043 p0044
  have p0046 :=
    @g_snelpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)
  have p0047 :=
    @g_sylibr (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)) (.classMem (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_cpw1 (syn_chnord A))) p0045 p0046
  have p0048 :=
    @g_hnsiquomapvalclndv A (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) hyp_hnsiquomappreexndv_1
  have p0049 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))))) p0047 p0048
  have p0050 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0051 :=
    @g_simpl (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0052 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0050 p0051
  have p0053 :=
    @g_pw1argclcl (syn_chwcn A) (.cv r)
  have p0054 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) p0052 p0053
  have p0055 :=
    @g_simpl (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0056 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0054 p0055
  have p0057 :=
    @g_hwnisoclasselhnordcl A (syn_cuni (.cv r)) hyp_hnsiquomappreexndv_1
  have p0058 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)) p0056 p0057
  have p0059 :=
    @g_elex (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)
  have p0060 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_chnord A)) (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_cvv)) p0058 p0059
  have p0061 :=
    @g_unisng (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_cvv)
  have p0062 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)) (syn_cvv)) (.classEq (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) p0060 p0061
  have p0063 :=
    @g_pw1eq (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))
  have p0064 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classEq (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (.classEq (syn_cpw1 (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) p0062 p0063
  have p0065 :=
    @g_imaeq2d (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_cpw1 (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_chnsicodemap A) p0064
  have p0066 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))))) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) p0049 p0065
  have p0067 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0068 :=
    @g_simpl (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0069 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0067 p0068
  have p0070 :=
    @g_pw1argclcl (syn_chwcn A) (.cv r)
  have p0071 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) p0069 p0070
  have p0072 :=
    @g_simpr (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0073 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))) p0071 p0072
  have p0074 :=
    @g_eceq1 (.cv r) (syn_csn (syn_cuni (.cv r))) (syn_csi (syn_chwniso A))
  have p0075 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))) (.classEq (syn_cec (.cv r) (syn_csi (syn_chwniso A))) (syn_cec (syn_csn (syn_cuni (.cv r))) (syn_csi (syn_chwniso A)))) p0073 p0074
  have p0076 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0077 :=
    @g_simpl (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0078 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0076 p0077
  have p0079 :=
    @g_pw1argclcl (syn_chwcn A) (.cv r)
  have p0080 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) p0078 p0079
  have p0081 :=
    @g_simpl (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0082 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0080 p0081
  have p0083 :=
    @g_elex (syn_cuni (.cv r)) (syn_chwcn A)
  have p0084 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) (.classMem (syn_cuni (.cv r)) (syn_cvv)) p0082 p0083
  have p0085 :=
    @g_siecsnclndv (syn_cuni (.cv r)) (syn_chwniso A)
  have p0086 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_cuni (.cv r)) (syn_cvv)) (.classEq (syn_cec (syn_csn (syn_cuni (.cv r))) (syn_csi (syn_chwniso A))) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) p0084 p0085
  have p0087 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_cec (.cv r) (syn_csi (syn_chwniso A))) (syn_cec (syn_csn (syn_cuni (.cv r))) (syn_csi (syn_chwniso A))) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) p0075 p0086
  have p0088 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_cec (.cv r) (syn_csi (syn_chwniso A))) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) p0087
  have p0089 :=
    @g_imaeq2d (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_cec (.cv r) (syn_csi (syn_chwniso A))) (syn_chnsicodemap A) p0088
  have p0090 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cima (syn_chnsicodemap A) (syn_cec (.cv r) (syn_csi (syn_chwniso A)))) p0066 p0089
  have p0091 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))
  have p0092 :=
    @g_simpl (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))
  have p0093 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0091 p0092
  have p0094 :=
    @g_hnsicodemapclassimcldndv A (.cv r) hyp_hnsiquomappreexndv_1
  have p0095 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (.cv r) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A)))) p0093 p0094
  have p0096 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cima (syn_chnsicodemap A) (syn_cec (.cv r) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))) p0090 p0095
  have p0097 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))) p0096
  have p0098 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.cv y) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwniso (syn_cpw1 A))) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) p0036 p0097
  have p0099 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.classMem (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_cpw1 (syn_chnord A))) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))) p0025 p0098
  have p0100 :=
    @g_id (.classEq (.cv x) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))
  have p0101 :=
    @g_fveq2d (.classEq (.cv x) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (.cv x) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_chnsiquomap A) p0100
  have p0102 :=
    @g_eqeq2d (.classEq (.cv x) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (syn_cfv (syn_chnsiquomap A) (.cv x)) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))) (.cv y) p0101
  have p0103 :=
    @g_rspcev (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))))) x (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_cpw1 (syn_chnord A)) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0102
  have p0104 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (syn_wa (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (syn_wa (.classMem (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A))) (syn_cpw1 (syn_chnord A))) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (syn_csn (syn_cec (syn_cuni (.cv r)) (syn_chwniso A)))))) (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x)))) p0099 p0103
  have p0105 :=
    @g_rexlimddv (syn_wa (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (syn_wa (.classMem (.cv w) (syn_chwcn (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))))) (.classEq (.cv w) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x)))) r (syn_cpw1 (syn_chwcn A)) dv_cache_0010 dv_cache_0011 p0014 p0104
  have p0106 :=
    @g_rexlimddv (.classMem (.cv y) (syn_chnord (syn_cpw1 A))) (.classEq (.cv y) (syn_cec (.cv w) (syn_chwniso (syn_cpw1 A)))) (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x)))) w (syn_chwcn (syn_cpw1 A)) dv_cache_0012 dv_cache_0013 p0006 p0105
  exact p0106

noncomputable def g_hnsiquomapfondv
    (A : Class) (hyp_hnsiquomapfondv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wfo (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
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
  have dv_cache_0004 : x ∉ ((syn_cpw1 (syn_chnord A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cpw1 (syn_chnord A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_chnord (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_chnord (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_chnsiquomap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_chnsiquomap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnsiquomapfndv A hyp_hnsiquomapfondv_1
  have p0001 :=
    @g_hnsiquomappreexndv x y A dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_hnsiquomapfondv_1
  have p0002 :=
    @g_rgen (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x)))) y (syn_chnord (syn_cpw1 A)) p0001
  have p0003 :=
    @g_pm3_2i (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wral y (syn_chnord (syn_cpw1 A)) (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))) p0000 p0002
  have p0004 :=
    @g_dffo3 x y (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) (syn_chnsiquomap A) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0003
  have p0005 :=
    @g_mpbir (syn_wfo (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wa (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wral y (syn_chnord (syn_cpw1 A)) (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x)))))) p0003 p0004
  exact p0005

noncomputable def g_hnsicodemapkernelcl2ndv
    (A : Class) (P : Class) (Q : Class) :
    Nominal.NPrf (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (.imp (.classMem P (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) P))))) := by
  let proofSupport : Finset Var := A.fv ∪ P.fv ∪ Q.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_P : r ∉ P.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_Q : r ∉ Q.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : r ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (Q).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ (P).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((Wff.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) P))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_Q, fresh_r_not_A, fresh_r_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_biid (.classMem Q (syn_cpw1 (syn_chwcn A)))
  have p0001 :=
    @g_a1i (syn_wb (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classMem Q (syn_cpw1 (syn_chwcn A)))) (.classEq (.cv r) P) p0000
  have p0002 :=
    @g_id (.classEq (.cv r) P)
  have p0003 :=
    @g_breq2d (.classEq (.cv r) P) (.cv r) P Q (syn_csi (syn_chwniso A)) p0002
  have p0004 :=
    @g_id (.classEq (.cv r) P)
  have p0005 :=
    @g_fveq2d (.classEq (.cv r) P) (.cv r) P (syn_chnsicodemap A) p0004
  have p0006 :=
    @g_breq2d (.classEq (.cv r) P) (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_cfv (syn_chnsicodemap A) P) (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) p0005
  have p0007 :=
    @g_bibi12d (.classEq (.cv r) P) (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr Q (syn_csi (syn_chwniso A)) P) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) P)) p0003 p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv r) P) (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classMem Q (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) P))) p0001 p0007
  have p0009 :=
    @g_hnsicodemapkernelclndv A Q r dv_cache_0001 dv_cache_0002
  have p0010 :=
    @g_com12 (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r)))) p0009
  have p0011 :=
    @g_vtoclga (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) (.cv r)) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) (.cv r))))) (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) P)))) r P (syn_cpw1 (syn_chwcn A)) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0008 p0010
  have p0012 :=
    @g_com12 (.classMem P (syn_cpw1 (syn_chwcn A))) (.classMem Q (syn_cpw1 (syn_chwcn A))) (syn_wb (syn_wbr Q (syn_csi (syn_chwniso A)) P) (syn_wbr (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)) (syn_cfv (syn_chnsicodemap A) P))) p0011
  exact p0012

#print axioms g_hnsicodemapkernelcl2ndv

end NFChoice.DirectNominalPrf.WPPReplay
