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
import NominalWPPReplayChunk016Compact001Part054

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

noncomputable def g_hnqinctrnrnssndv
    (A : Class) (D : Class) (E : Class) (F : Class) (hyp_hnqinctrnrnssndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hnqinctrnrnssndv_2 : Nominal.NPrf (syn_wf1o F D E)) (hyp_hnqinctrnrnssndv_3 : Nominal.NPrf (syn_wss D A)) (hyp_hnqinctrnrnssndv_4 : Nominal.NPrf (syn_wss E A)) (hyp_hnqinctrnrnssndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wss (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ E.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_F : u ∉ F.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have dv_cache_0001 : x ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_chnqinc D A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0006 : u ∉ ((Wff.classMem (.cv y) (syn_crn (syn_chnqinc E A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_y, fresh_u_not_A, fresh_u_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_not_A, fresh_u_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (.cv y) (syn_crn (syn_chnqinc E A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_A, fresh_x_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_crn (syn_chnqinc D A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_crn (syn_chnqinc E A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elrn x (.cv y) (syn_chnqinc D A) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_breldm (.cv x) (.cv y) (syn_chnqinc D A)
  have p0002 :=
    @g_f1odm D E F
  have p0003 :=
    Nominal.mp hyp_hnqinctrnrnssndv_2 p0002
  have p0004 :=
    @g_dmex F hyp_hnqinctrnrnssndv_1
  have p0005 :=
    @g_eqeltrri (syn_cdm F) D (syn_cvv) p0003 p0004
  have p0006 :=
    @g_hnqincdm A D hyp_hnqinctrnrnssndv_3 p0005 hyp_hnqinctrnrnssndv_5
  have p0007 :=
    @g_eleq2i (syn_cdm (syn_chnqinc D A)) (syn_chnord D) (.cv x) p0006
  have p0008 :=
    @g_sylib (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (.classMem (.cv x) (syn_cdm (syn_chnqinc D A))) (.classMem (.cv x) (syn_chnord D)) p0001 p0007
  have p0009 :=
    @g_vex x
  have p0010 :=
    @g_elhnord x u D dv_cache_0003 dv_cache_0004 dv_cache_0005 p0009
  have p0011 :=
    @g_id (syn_wrex u (syn_chwcn D) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
  have p0012 :=
    @g_sylbi (.classMem (.cv x) (syn_chnord D)) (syn_wrex u (syn_chwcn D) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))) (syn_wrex u (syn_chwcn D) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))) p0010 p0011
  have p0013 :=
    @g_syl (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (.classMem (.cv x) (syn_chnord D)) (syn_wrex u (syn_chwcn D) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))) p0008 p0012
  have p0014 :=
    @g_simpr (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
  have p0015 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))
  have p0016 :=
    @g_syl (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))) p0014 p0015
  have p0017 :=
    @g_fveq2d (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (.cv x) (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqinc D A) p0016
  have p0018 :=
    @g_simpl (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
  have p0019 :=
    @g_f1odm D E F
  have p0020 :=
    Nominal.mp hyp_hnqinctrnrnssndv_2 p0019
  have p0021 :=
    @g_dmex F hyp_hnqinctrnrnssndv_1
  have p0022 :=
    @g_eqeltrri (syn_cdm F) D (syn_cvv) p0020 p0021
  have p0023 :=
    @g_hnqincfn A D hyp_hnqinctrnrnssndv_3 p0022 hyp_hnqinctrnrnssndv_5
  have p0024 :=
    @g_fnfun (syn_chnord D) (syn_chnqinc D A)
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_funbrfv (.cv x) (.cv y) (syn_chnqinc D A)
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (.cv y)) p0018 p0027
  have p0029 :=
    @g_eqtr3d (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (syn_cfv (syn_chnqinc D A) (.cv x)) (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (.cv y) p0017 p0028
  have p0030 :=
    @g_simpr (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
  have p0031 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))
  have p0032 :=
    @g_syl (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))) (.classMem (.cv u) (syn_chwcn D)) p0030 p0031
  have p0033 :=
    @g_hnqinctrnvaldndv u A D E F hyp_hnqinctrnrnssndv_1 hyp_hnqinctrnrnssndv_2 hyp_hnqinctrnrnssndv_3 hyp_hnqinctrnrnssndv_4 hyp_hnqinctrnrnssndv_5
  have p0034 :=
    @g_syl (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (.classMem (.cv u) (syn_chwcn D)) (.classEq (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (syn_cfv (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))) p0032 p0033
  have p0035 :=
    @g_eqtr3d (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (.cv y) (syn_cfv (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) p0029 p0034
  have p0036 :=
    @g_f1ofo D E F
  have p0037 :=
    Nominal.mp hyp_hnqinctrnrnssndv_2 p0036
  have p0038 :=
    @g_forn D E F
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_rnex F hyp_hnqinctrnrnssndv_1
  have p0041 :=
    @g_eqeltrri (syn_crn F) E (syn_cvv) p0039 p0040
  have p0042 :=
    @g_hnqincfn A E hyp_hnqinctrnrnssndv_4 p0041 hyp_hnqinctrnrnssndv_5
  have p0043 :=
    @g_a1i (syn_wfn (syn_chnqinc E A) (syn_chnord E)) (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) p0042
  have p0044 :=
    @g_simpr (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
  have p0045 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))
  have p0046 :=
    @g_syl (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))) (.classMem (.cv u) (syn_chwcn D)) p0044 p0045
  have p0047 :=
    @g_hncodetrncndndv u D E F hyp_hnqinctrnrnssndv_1 hyp_hnqinctrnrnssndv_2
  have p0048 :=
    @g_syl (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (.classMem (.cv u) (syn_chwcn D)) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)) p0046 p0047
  have p0049 :=
    @g_f1ofo D E F
  have p0050 :=
    Nominal.mp hyp_hnqinctrnrnssndv_2 p0049
  have p0051 :=
    @g_forn D E F
  have p0052 :=
    Nominal.mp p0050 p0051
  have p0053 :=
    @g_rnex F hyp_hnqinctrnrnssndv_1
  have p0054 :=
    @g_eqeltrri (syn_crn F) E (syn_cvv) p0052 p0053
  have p0055 :=
    @g_hwnisoclasselhnordcl E (syn_cfv (syn_chncodetrnfn F) (.cv u)) p0054
  have p0056 :=
    @g_syl (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)) (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnord E)) p0048 p0055
  have p0057 :=
    @g_jca (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (syn_wfn (syn_chnqinc E A) (syn_chnord E)) (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnord E)) p0043 p0056
  have p0058 :=
    @g_fnfvelrn (syn_chnord E) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnqinc E A)
  have p0059 :=
    @g_syl (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (syn_wa (syn_wfn (syn_chnqinc E A) (syn_chnord E)) (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnord E))) (.classMem (syn_cfv (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) (syn_crn (syn_chnqinc E A))) p0057 p0058
  have p0060 :=
    @g_eqeltrd (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (syn_wa (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))) (.cv y) (syn_cfv (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))) (syn_crn (syn_chnqinc E A)) p0035 p0059
  have p0061 :=
    @g_rexlimddv (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))) (.classMem (.cv y) (syn_crn (syn_chnqinc E A))) u (syn_chwcn D) dv_cache_0006 dv_cache_0007 p0013 p0060
  have p0062 :=
    @g_exlimiv (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (.classMem (.cv y) (syn_crn (syn_chnqinc E A))) x dv_cache_0008 p0061
  have p0063 :=
    @g_sylbi (.classMem (.cv y) (syn_crn (syn_chnqinc D A))) (syn_wex x (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))) (.classMem (.cv y) (syn_crn (syn_chnqinc E A))) p0000 p0062
  have p0064 :=
    @g_ssriv y (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A)) dv_cache_0009 dv_cache_0010 p0063
  exact p0064

noncomputable def g_hnqinctrnrneqndv
    (A : Class) (D : Class) (E : Class) (F : Class) (hyp_hnqinctrnrneqndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hnqinctrnrneqndv_2 : Nominal.NPrf (syn_wf1o F D E)) (hyp_hnqinctrnrneqndv_3 : Nominal.NPrf (syn_wss D A)) (hyp_hnqinctrnrneqndv_4 : Nominal.NPrf (syn_wss E A)) (hyp_hnqinctrnrneqndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ E.fv ∪ F.fv
  have p0000 :=
    @g_hnqinctrnrnssndv A D E F hyp_hnqinctrnrneqndv_1 hyp_hnqinctrnrneqndv_2 hyp_hnqinctrnrneqndv_3 hyp_hnqinctrnrneqndv_4 hyp_hnqinctrnrneqndv_5
  have p0001 :=
    @g_cnvex F hyp_hnqinctrnrneqndv_1
  have p0002 :=
    @g_f1ocnv D E F
  have p0003 :=
    Nominal.mp hyp_hnqinctrnrneqndv_2 p0002
  have p0004 :=
    @g_hnqinctrnrnssndv A E D (syn_ccnv F) p0001 p0003 hyp_hnqinctrnrneqndv_4 hyp_hnqinctrnrneqndv_3 hyp_hnqinctrnrneqndv_5
  have p0005 :=
    @g_eqssi (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A)) p0000 p0004
  exact p0005

noncomputable def g_hnordf1oenambndv
    (A : Class) (D : Class) (E : Class) (F : Class) (hyp_hnordf1oenambndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hnordf1oenambndv_2 : Nominal.NPrf (syn_wf1o F D E)) (hyp_hnordf1oenambndv_3 : Nominal.NPrf (syn_wss D A)) (hyp_hnordf1oenambndv_4 : Nominal.NPrf (syn_wss E A)) (hyp_hnordf1oenambndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_chnord D) (syn_cen) (syn_chnord E)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ E.fv ∪ F.fv
  have p0000 :=
    @g_f1odm D E F
  have p0001 :=
    Nominal.mp hyp_hnordf1oenambndv_2 p0000
  have p0002 :=
    @g_dmex F hyp_hnordf1oenambndv_1
  have p0003 :=
    @g_eqeltrri (syn_cdm F) D (syn_cvv) p0001 p0002
  have p0004 :=
    @g_hnqincf1 A D hyp_hnordf1oenambndv_3 p0003 hyp_hnordf1oenambndv_5
  have p0005 :=
    @g_f1f1orn (syn_chnord D) (syn_chnord A) (syn_chnqinc D A)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_f1odm D E F
  have p0008 :=
    Nominal.mp hyp_hnordf1oenambndv_2 p0007
  have p0009 :=
    @g_dmex F hyp_hnordf1oenambndv_1
  have p0010 :=
    @g_eqeltrri (syn_cdm F) D (syn_cvv) p0008 p0009
  have p0011 :=
    @g_pm3_2i (.classMem D (syn_cvv)) (.classMem A (syn_cvv)) p0010 hyp_hnordf1oenambndv_5
  have p0012 :=
    @g_hnqincexg A D
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_f1oen (syn_chnord D) (syn_crn (syn_chnqinc D A)) (syn_chnqinc D A) p0013
  have p0015 :=
    Nominal.mp p0006 p0014
  have p0016 :=
    @g_f1ofo D E F
  have p0017 :=
    Nominal.mp hyp_hnordf1oenambndv_2 p0016
  have p0018 :=
    @g_forn D E F
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_rnex F hyp_hnordf1oenambndv_1
  have p0021 :=
    @g_eqeltrri (syn_crn F) E (syn_cvv) p0019 p0020
  have p0022 :=
    @g_hnqincf1 A E hyp_hnordf1oenambndv_4 p0021 hyp_hnordf1oenambndv_5
  have p0023 :=
    @g_f1f1orn (syn_chnord E) (syn_chnord A) (syn_chnqinc E A)
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_f1ofo D E F
  have p0026 :=
    Nominal.mp hyp_hnordf1oenambndv_2 p0025
  have p0027 :=
    @g_forn D E F
  have p0028 :=
    Nominal.mp p0026 p0027
  have p0029 :=
    @g_rnex F hyp_hnordf1oenambndv_1
  have p0030 :=
    @g_eqeltrri (syn_crn F) E (syn_cvv) p0028 p0029
  have p0031 :=
    @g_pm3_2i (.classMem E (syn_cvv)) (.classMem A (syn_cvv)) p0030 hyp_hnordf1oenambndv_5
  have p0032 :=
    @g_hnqincexg A E
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_f1oen (syn_chnord E) (syn_crn (syn_chnqinc E A)) (syn_chnqinc E A) p0033
  have p0035 :=
    Nominal.mp p0024 p0034
  have p0036 :=
    @g_ensymi (syn_chnord E) (syn_crn (syn_chnqinc E A))
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_hnqinctrnrneqndv A D E F hyp_hnordf1oenambndv_1 hyp_hnordf1oenambndv_2 hyp_hnordf1oenambndv_3 hyp_hnordf1oenambndv_4 hyp_hnordf1oenambndv_5
  have p0039 :=
    @g_breq1i (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A)) (syn_chnord E) (syn_cen) p0038
  have p0040 :=
    @g_mpbir (syn_wbr (syn_crn (syn_chnqinc D A)) (syn_cen) (syn_chnord E)) (syn_wbr (syn_crn (syn_chnqinc E A)) (syn_cen) (syn_chnord E)) p0037 p0039
  have p0041 :=
    @g_pm3_2i (syn_wbr (syn_chnord D) (syn_cen) (syn_crn (syn_chnqinc D A))) (syn_wbr (syn_crn (syn_chnqinc D A)) (syn_cen) (syn_chnord E)) p0015 p0040
  have p0042 :=
    @g_entr (syn_chnord D) (syn_crn (syn_chnqinc D A)) (syn_chnord E)
  have p0043 :=
    Nominal.mp p0041 p0042
  exact p0043

noncomputable def g_hncardf1oeqambndv
    (A : Class) (D : Class) (E : Class) (F : Class) (hyp_hncardf1oeqambndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hncardf1oeqambndv_2 : Nominal.NPrf (syn_wf1o F D E)) (hyp_hncardf1oeqambndv_3 : Nominal.NPrf (syn_wss D A)) (hyp_hncardf1oeqambndv_4 : Nominal.NPrf (syn_wss E A)) (hyp_hncardf1oeqambndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_chncard D) (syn_chncard E)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ E.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard D)))
  have p0001 :=
    @g_hnordf1oenambndv A D E F hyp_hncardf1oeqambndv_1 hyp_hncardf1oeqambndv_2 hyp_hncardf1oeqambndv_3 hyp_hncardf1oeqambndv_4 hyp_hncardf1oeqambndv_5
  have p0002 :=
    @g_f1odm D E F
  have p0003 :=
    Nominal.mp hyp_hncardf1oeqambndv_2 p0002
  have p0004 :=
    @g_dmex F hyp_hncardf1oeqambndv_1
  have p0005 :=
    @g_eqeltrri (syn_cdm F) D (syn_cvv) p0003 p0004
  have p0006 :=
    @g_hnordexg D
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_eqnc (syn_chnord D) (syn_chnord E) p0007
  have p0009 :=
    @g_mpbir (.classEq (syn_cnc (syn_chnord D)) (syn_cnc (syn_chnord E))) (syn_wbr (syn_chnord D) (syn_cen) (syn_chnord E)) p0001 p0008
  have p0010 :=
    @g_eqtri (syn_chncard D) (syn_cnc (syn_chnord D)) (syn_cnc (syn_chnord E)) p0000 p0009
  have p0011 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard E)))
  have p0012 :=
    @g_eqtr4i (syn_chncard D) (syn_cnc (syn_chnord E)) (syn_chncard E) p0010 p0011
  exact p0012

noncomputable def g_hncardf1oeqndv
    (D : Class) (E : Class) (F : Class) (hyp_hncardf1oeqndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hncardf1oeqndv_2 : Nominal.NPrf (syn_wf1o F D E)) :
    Nominal.NPrf (.classEq (syn_chncard D) (syn_chncard E)) := by
  let proofSupport : Finset Var := D.fv ∪ E.fv ∪ F.fv
  have p0000 :=
    @g_ssun1 D E
  have p0001 :=
    @g_ssun2 E D
  have p0002 :=
    @g_f1odm D E F
  have p0003 :=
    Nominal.mp hyp_hncardf1oeqndv_2 p0002
  have p0004 :=
    @g_dmex F hyp_hncardf1oeqndv_1
  have p0005 :=
    @g_eqeltrri (syn_cdm F) D (syn_cvv) p0003 p0004
  have p0006 :=
    @g_f1ofo D E F
  have p0007 :=
    Nominal.mp hyp_hncardf1oeqndv_2 p0006
  have p0008 :=
    @g_forn D E F
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_rnex F hyp_hncardf1oeqndv_1
  have p0011 :=
    @g_eqeltrri (syn_crn F) E (syn_cvv) p0009 p0010
  have p0012 :=
    @g_unex D E p0005 p0011
  have p0013 :=
    @g_hncardf1oeqambndv (syn_cun D E) D E F hyp_hncardf1oeqndv_1 hyp_hncardf1oeqndv_2 p0000 p0001 p0012
  exact p0013

noncomputable def g_hnordeqdndv
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_chnord A) (syn_chnord B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0001 :=
    @g_a1i (.classEq (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A))) (.classEq A B) p0000
  have p0002 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0003 :=
    @g_a1i (.classEq (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels))) (.classEq A B) p0002
  have p0004 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0005 :=
    @g_a1i (.classEq (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (.classEq A B) p0004
  have p0006 :=
    @g_pweq A B
  have p0007 :=
    @g_xpeq2d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_cvv) p0006
  have p0008 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cxp (syn_cvv) (syn_cpw B)) (syn_cwe) p0007
  have p0009 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0005 p0008
  have p0010 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes B)))
  have p0011 :=
    @g_eqcomi (syn_chwcodes B) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0010
  have p0012 :=
    @g_a1i (.classEq (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B)) (.classEq A B) p0011
  have p0013 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B) p0009 p0012
  have p0014 :=
    @g_ineq1d (.classEq A B) (syn_chwcodes A) (syn_chwcodes B) (syn_chwrels) p0013
  have p0015 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0003 p0014
  have p0016 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn B)))
  have p0017 :=
    @g_eqcomi (syn_chwcn B) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0016
  have p0018 :=
    @g_a1i (.classEq (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B)) (.classEq A B) p0017
  have p0019 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B) p0015 p0018
  have p0020 :=
    @g_qseq1 (syn_chwcn A) (syn_chwcn B) (syn_chwniso A)
  have p0021 :=
    @g_syl (.classEq A B) (.classEq (syn_chwcn A) (syn_chwcn B)) (.classEq (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso A))) p0019 p0020
  have p0022 :=
    (by simpa [syn_chwniso] using (Nominal.classEqRefl (syn_chwniso A)))
  have p0023 :=
    @g_a1i (.classEq (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) (.classEq A B) p0022
  have p0024 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0025 :=
    @g_a1i (.classEq (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels))) (.classEq A B) p0024
  have p0026 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0027 :=
    @g_a1i (.classEq (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (.classEq A B) p0026
  have p0028 :=
    @g_pweq A B
  have p0029 :=
    @g_xpeq2d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_cvv) p0028
  have p0030 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cxp (syn_cvv) (syn_cpw B)) (syn_cwe) p0029
  have p0031 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0027 p0030
  have p0032 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes B)))
  have p0033 :=
    @g_eqcomi (syn_chwcodes B) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0032
  have p0034 :=
    @g_a1i (.classEq (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B)) (.classEq A B) p0033
  have p0035 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B) p0031 p0034
  have p0036 :=
    @g_ineq1d (.classEq A B) (syn_chwcodes A) (syn_chwcodes B) (syn_chwrels) p0035
  have p0037 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0025 p0036
  have p0038 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn B)))
  have p0039 :=
    @g_eqcomi (syn_chwcn B) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0038
  have p0040 :=
    @g_a1i (.classEq (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B)) (.classEq A B) p0039
  have p0041 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B) p0037 p0040
  have p0042 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0043 :=
    @g_a1i (.classEq (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels))) (.classEq A B) p0042
  have p0044 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0045 :=
    @g_a1i (.classEq (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (.classEq A B) p0044
  have p0046 :=
    @g_pweq A B
  have p0047 :=
    @g_xpeq2d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_cvv) p0046
  have p0048 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cxp (syn_cvv) (syn_cpw B)) (syn_cwe) p0047
  have p0049 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0045 p0048
  have p0050 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes B)))
  have p0051 :=
    @g_eqcomi (syn_chwcodes B) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0050
  have p0052 :=
    @g_a1i (.classEq (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B)) (.classEq A B) p0051
  have p0053 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B) p0049 p0052
  have p0054 :=
    @g_ineq1d (.classEq A B) (syn_chwcodes A) (syn_chwcodes B) (syn_chwrels) p0053
  have p0055 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0043 p0054
  have p0056 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn B)))
  have p0057 :=
    @g_eqcomi (syn_chwcn B) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0056
  have p0058 :=
    @g_a1i (.classEq (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B)) (.classEq A B) p0057
  have p0059 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B) p0055 p0058
  have p0060 :=
    @g_xpeq12d (.classEq A B) (syn_chwcn A) (syn_chwcn B) (syn_chwcn A) (syn_chwcn B) p0041 p0059
  have p0061 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cxp (syn_chwcn B) (syn_chwcn B)) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) p0060
  have p0062 :=
    @g_eqtrd (.classEq A B) (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn B) (syn_chwcn B))) p0023 p0061
  have p0063 :=
    (by simpa [syn_chwniso] using (Nominal.classEqRefl (syn_chwniso B)))
  have p0064 :=
    @g_eqcomi (syn_chwniso B) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn B) (syn_chwcn B))) p0063
  have p0065 :=
    @g_a1i (.classEq (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn B) (syn_chwcn B))) (syn_chwniso B)) (.classEq A B) p0064
  have p0066 :=
    @g_eqtrd (.classEq A B) (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn B) (syn_chwcn B))) (syn_chwniso B) p0062 p0065
  have p0067 :=
    @g_qseq2 (syn_chwniso A) (syn_chwniso B) (syn_chwcn B)
  have p0068 :=
    @g_syl (.classEq A B) (.classEq (syn_chwniso A) (syn_chwniso B)) (.classEq (syn_cqs (syn_chwcn B) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B))) p0066 p0067
  have p0069 :=
    @g_eqtrd (.classEq A B) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0021 p0068
  have p0070 :=
    @g_eqtrd (.classEq A B) (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0001 p0069
  have p0071 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord B)))
  have p0072 :=
    @g_eqcomi (syn_chnord B) (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0071
  have p0073 :=
    @g_a1i (.classEq (syn_cqs (syn_chwcn B) (syn_chwniso B)) (syn_chnord B)) (.classEq A B) p0072
  have p0074 :=
    @g_eqtrd (.classEq A B) (syn_chnord A) (syn_cqs (syn_chwcn B) (syn_chwniso B)) (syn_chnord B) p0070 p0073
  exact p0074

noncomputable def g_hncardeqdndv
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_chncard A) (syn_chncard B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard A)))
  have p0001 :=
    @g_a1i (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))) (.classEq A B) p0000
  have p0002 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0003 :=
    @g_a1i (.classEq (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A))) (.classEq A B) p0002
  have p0004 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0005 :=
    @g_a1i (.classEq (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels))) (.classEq A B) p0004
  have p0006 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0007 :=
    @g_a1i (.classEq (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (.classEq A B) p0006
  have p0008 :=
    @g_pweq A B
  have p0009 :=
    @g_xpeq2d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_cvv) p0008
  have p0010 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cxp (syn_cvv) (syn_cpw B)) (syn_cwe) p0009
  have p0011 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0007 p0010
  have p0012 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes B)))
  have p0013 :=
    @g_eqcomi (syn_chwcodes B) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0012
  have p0014 :=
    @g_a1i (.classEq (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B)) (.classEq A B) p0013
  have p0015 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B) p0011 p0014
  have p0016 :=
    @g_ineq1d (.classEq A B) (syn_chwcodes A) (syn_chwcodes B) (syn_chwrels) p0015
  have p0017 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0005 p0016
  have p0018 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn B)))
  have p0019 :=
    @g_eqcomi (syn_chwcn B) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0018
  have p0020 :=
    @g_a1i (.classEq (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B)) (.classEq A B) p0019
  have p0021 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B) p0017 p0020
  have p0022 :=
    @g_qseq1 (syn_chwcn A) (syn_chwcn B) (syn_chwniso A)
  have p0023 :=
    @g_syl (.classEq A B) (.classEq (syn_chwcn A) (syn_chwcn B)) (.classEq (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso A))) p0021 p0022
  have p0024 :=
    (by simpa [syn_chwniso] using (Nominal.classEqRefl (syn_chwniso A)))
  have p0025 :=
    @g_a1i (.classEq (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) (.classEq A B) p0024
  have p0026 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0027 :=
    @g_a1i (.classEq (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels))) (.classEq A B) p0026
  have p0028 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0029 :=
    @g_a1i (.classEq (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (.classEq A B) p0028
  have p0030 :=
    @g_pweq A B
  have p0031 :=
    @g_xpeq2d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_cvv) p0030
  have p0032 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cxp (syn_cvv) (syn_cpw B)) (syn_cwe) p0031
  have p0033 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0029 p0032
  have p0034 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes B)))
  have p0035 :=
    @g_eqcomi (syn_chwcodes B) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0034
  have p0036 :=
    @g_a1i (.classEq (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B)) (.classEq A B) p0035
  have p0037 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B) p0033 p0036
  have p0038 :=
    @g_ineq1d (.classEq A B) (syn_chwcodes A) (syn_chwcodes B) (syn_chwrels) p0037
  have p0039 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0027 p0038
  have p0040 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn B)))
  have p0041 :=
    @g_eqcomi (syn_chwcn B) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0040
  have p0042 :=
    @g_a1i (.classEq (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B)) (.classEq A B) p0041
  have p0043 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B) p0039 p0042
  have p0044 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0045 :=
    @g_a1i (.classEq (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels))) (.classEq A B) p0044
  have p0046 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes A)))
  have p0047 :=
    @g_a1i (.classEq (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) (.classEq A B) p0046
  have p0048 :=
    @g_pweq A B
  have p0049 :=
    @g_xpeq2d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_cvv) p0048
  have p0050 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cxp (syn_cvv) (syn_cpw B)) (syn_cwe) p0049
  have p0051 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0047 p0050
  have p0052 :=
    (by simpa [syn_chwcodes] using (Nominal.classEqRefl (syn_chwcodes B)))
  have p0053 :=
    @g_eqcomi (syn_chwcodes B) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0052
  have p0054 :=
    @g_a1i (.classEq (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B)) (.classEq A B) p0053
  have p0055 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B) p0051 p0054
  have p0056 :=
    @g_ineq1d (.classEq A B) (syn_chwcodes A) (syn_chwcodes B) (syn_chwrels) p0055
  have p0057 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0045 p0056
  have p0058 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn B)))
  have p0059 :=
    @g_eqcomi (syn_chwcn B) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0058
  have p0060 :=
    @g_a1i (.classEq (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B)) (.classEq A B) p0059
  have p0061 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B) p0057 p0060
  have p0062 :=
    @g_xpeq12d (.classEq A B) (syn_chwcn A) (syn_chwcn B) (syn_chwcn A) (syn_chwcn B) p0043 p0061
  have p0063 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cxp (syn_chwcn B) (syn_chwcn B)) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) p0062
  have p0064 :=
    @g_eqtrd (.classEq A B) (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn B) (syn_chwcn B))) p0025 p0063
  have p0065 :=
    (by simpa [syn_chwniso] using (Nominal.classEqRefl (syn_chwniso B)))
  have p0066 :=
    @g_eqcomi (syn_chwniso B) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn B) (syn_chwcn B))) p0065
  have p0067 :=
    @g_a1i (.classEq (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn B) (syn_chwcn B))) (syn_chwniso B)) (.classEq A B) p0066
  have p0068 :=
    @g_eqtrd (.classEq A B) (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn B) (syn_chwcn B))) (syn_chwniso B) p0064 p0067
  have p0069 :=
    @g_qseq2 (syn_chwniso A) (syn_chwniso B) (syn_chwcn B)
  have p0070 :=
    @g_syl (.classEq A B) (.classEq (syn_chwniso A) (syn_chwniso B)) (.classEq (syn_cqs (syn_chwcn B) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B))) p0068 p0069
  have p0071 :=
    @g_eqtrd (.classEq A B) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0023 p0070
  have p0072 :=
    @g_eqtrd (.classEq A B) (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0003 p0071
  have p0073 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord B)))
  have p0074 :=
    @g_eqcomi (syn_chnord B) (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0073
  have p0075 :=
    @g_a1i (.classEq (syn_cqs (syn_chwcn B) (syn_chwniso B)) (syn_chnord B)) (.classEq A B) p0074
  have p0076 :=
    @g_eqtrd (.classEq A B) (syn_chnord A) (syn_cqs (syn_chwcn B) (syn_chwniso B)) (syn_chnord B) p0072 p0075
  have p0077 :=
    @g_nceqd (.classEq A B) (syn_chnord A) (syn_chnord B) p0076
  have p0078 :=
    @g_eqtrd (.classEq A B) (syn_chncard A) (syn_cnc (syn_chnord A)) (syn_cnc (syn_chnord B)) p0001 p0077
  have p0079 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard B)))
  have p0080 :=
    @g_eqcomi (syn_chncard B) (syn_cnc (syn_chnord B)) p0079
  have p0081 :=
    @g_a1i (.classEq (syn_cnc (syn_chnord B)) (syn_chncard B)) (.classEq A B) p0080
  have p0082 :=
    @g_eqtrd (.classEq A B) (syn_chncard A) (syn_cnc (syn_chnord B)) (syn_chncard B) p0078 p0081
  exact p0082

noncomputable def g_hncardf1oimpndv
    (D : Class) (E : Class) (F : Class) (hyp_hncardf1oimpndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wf1o F D E) (.classEq (syn_chncard D) (syn_chncard E))) := by
  let proofSupport : Finset Var := D.fv ∪ E.fv ∪ F.fv
  have p0000 :=
    @g_iftrue (syn_wf1o F D E) D (syn_c0)
  have p0001 :=
    @g_hncardeqdndv (syn_cif (syn_wf1o F D E) D (syn_c0)) D
  have p0002 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) D (syn_c0)) D) (.classEq (syn_chncard (syn_cif (syn_wf1o F D E) D (syn_c0))) (syn_chncard D)) p0000 p0001
  have p0003 :=
    @g_eqcomd (syn_wf1o F D E) (syn_chncard (syn_cif (syn_wf1o F D E) D (syn_c0))) (syn_chncard D) p0002
  have p0004 :=
    @g_n_0ex
  have p0005 :=
    @g_ifex (syn_wf1o F D E) F (syn_c0) hyp_hncardf1oimpndv_1 p0004
  have p0006 :=
    @g_id (syn_wf1o F D E)
  have p0007 :=
    @g_iftrue (syn_wf1o F D E) F (syn_c0)
  have p0008 :=
    @g_f1oeq1 (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)) (syn_cif (syn_wf1o F D E) F (syn_c0)) F
  have p0009 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) F (syn_c0)) F) (syn_wb (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)))) p0007 p0008
  have p0010 :=
    @g_iftrue (syn_wf1o F D E) D (syn_c0)
  have p0011 :=
    @g_f1oeq2 (syn_cif (syn_wf1o F D E) D (syn_c0)) D (syn_cif (syn_wf1o F D E) E (syn_c0)) F
  have p0012 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) D (syn_c0)) D) (syn_wb (syn_wf1o F (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F D (syn_cif (syn_wf1o F D E) E (syn_c0)))) p0010 p0011
  have p0013 :=
    @g_bitrd (syn_wf1o F D E) (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F D (syn_cif (syn_wf1o F D E) E (syn_c0))) p0009 p0012
  have p0014 :=
    @g_iftrue (syn_wf1o F D E) E (syn_c0)
  have p0015 :=
    @g_f1oeq3 (syn_cif (syn_wf1o F D E) E (syn_c0)) E D F
  have p0016 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) E (syn_c0)) E) (syn_wb (syn_wf1o F D (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F D E)) p0014 p0015
  have p0017 :=
    @g_bitrd (syn_wf1o F D E) (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F D (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F D E) p0013 p0016
  have p0018 :=
    @g_mpbird (syn_wf1o F D E) (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F D E) p0006 p0017
  have p0019 :=
    @g_f1o0
  have p0020 :=
    @g_iffalse (syn_wf1o F D E) F (syn_c0)
  have p0021 :=
    @g_f1oeq1 (syn_c0) (syn_c0) (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0)
  have p0022 :=
    @g_syl (.neg (syn_wf1o F D E)) (.classEq (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0)) (syn_wb (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0) (syn_c0)) (syn_wf1o (syn_c0) (syn_c0) (syn_c0))) p0020 p0021
  have p0023 :=
    @g_mpbiri (.neg (syn_wf1o F D E)) (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0) (syn_c0)) (syn_wf1o (syn_c0) (syn_c0) (syn_c0)) p0019 p0022
  have p0024 :=
    @g_iffalse (syn_wf1o F D E) D (syn_c0)
  have p0025 :=
    @g_iffalse (syn_wf1o F D E) E (syn_c0)
  have p0026 :=
    @g_jca (.neg (syn_wf1o F D E)) (.classEq (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_c0)) (.classEq (syn_cif (syn_wf1o F D E) E (syn_c0)) (syn_c0)) p0024 p0025
  have p0027 :=
    @g_f1oeq23 (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_c0) (syn_cif (syn_wf1o F D E) E (syn_c0)) (syn_c0) (syn_cif (syn_wf1o F D E) F (syn_c0))
  have p0028 :=
    @g_syl (.neg (syn_wf1o F D E)) (syn_wa (.classEq (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_c0)) (.classEq (syn_cif (syn_wf1o F D E) E (syn_c0)) (syn_c0))) (syn_wb (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0) (syn_c0))) p0026 p0027
  have p0029 :=
    @g_mpbird (.neg (syn_wf1o F D E)) (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0) (syn_c0)) p0023 p0028
  have p0030 :=
    @g_pm2_61i (syn_wf1o F D E) (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))) p0018 p0029
  have p0031 :=
    @g_hncardf1oeqndv (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)) (syn_cif (syn_wf1o F D E) F (syn_c0)) p0005 p0030
  have p0032 :=
    @g_a1i (.classEq (syn_chncard (syn_cif (syn_wf1o F D E) D (syn_c0))) (syn_chncard (syn_cif (syn_wf1o F D E) E (syn_c0)))) (syn_wf1o F D E) p0031
  have p0033 :=
    @g_eqtrd (syn_wf1o F D E) (syn_chncard D) (syn_chncard (syn_cif (syn_wf1o F D E) D (syn_c0))) (syn_chncard (syn_cif (syn_wf1o F D E) E (syn_c0))) p0003 p0032
  have p0034 :=
    @g_iftrue (syn_wf1o F D E) E (syn_c0)
  have p0035 :=
    @g_hncardeqdndv (syn_cif (syn_wf1o F D E) E (syn_c0)) E
  have p0036 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) E (syn_c0)) E) (.classEq (syn_chncard (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_chncard E)) p0034 p0035
  have p0037 :=
    @g_eqtrd (syn_wf1o F D E) (syn_chncard D) (syn_chncard (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_chncard E) p0033 p0036
  exact p0037

noncomputable def g_hncardnceqdndv
    (D : Class) (E : Class) (hyp_hncardnceqdndv_1 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hncardnceqdndv_2 : Nominal.NPrf (.classMem E (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (syn_cnc D) (syn_cnc E)) (.classEq (syn_chncard D) (syn_chncard E))) := by
  let proofSupport : Finset Var := D.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ (E).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.classEq (syn_chncard D) (syn_chncard E))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqnc D E hyp_hncardnceqdndv_1
  have p0001 :=
    @g_biimpi (.classEq (syn_cnc D) (syn_cnc E)) (syn_wbr D (syn_cen) E) p0000
  have p0002 :=
    @g_bren D E f dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_biimpi (syn_wbr D (syn_cen) E) (syn_wex f (syn_wf1o (.cv f) D E)) p0002
  have p0004 :=
    @g_syl (.classEq (syn_cnc D) (syn_cnc E)) (syn_wbr D (syn_cen) E) (syn_wex f (syn_wf1o (.cv f) D E)) p0001 p0003
  have p0005 :=
    @g_vex f
  have p0006 :=
    @g_hncardf1oimpndv D E (.cv f) p0005
  have p0007 :=
    @g_exlimiv (syn_wf1o (.cv f) D E) (.classEq (syn_chncard D) (syn_chncard E)) f dv_cache_0003 p0006
  have p0008 :=
    @g_syl (.classEq (syn_cnc D) (syn_cnc E)) (syn_wex f (syn_wf1o (.cv f) D E)) (.classEq (syn_chncard D) (syn_chncard E)) p0004 p0007
  exact p0008

noncomputable def g_hncardnceqndv
    (D : Class) (E : Class) (hyp_hncardnceqndv_1 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hncardnceqndv_2 : Nominal.NPrf (.classMem E (syn_cvv))) (hyp_hncardnceqndv_3 : Nominal.NPrf (.classEq (syn_cnc D) (syn_cnc E))) :
    Nominal.NPrf (.classEq (syn_chncard D) (syn_chncard E)) := by
  let proofSupport : Finset Var := D.fv ∪ E.fv
  have p0000 :=
    @g_hncardnceqdndv D E hyp_hncardnceqndv_1 hyp_hncardnceqndv_2
  have p0001 :=
    Nominal.mp hyp_hncardnceqndv_3 p0000
  exact p0001

noncomputable def g_wppcardt4fnexndv
     :
    Nominal.NPrf (.classMem (syn_cwppcardt4fn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwppcardt4fn] using (Nominal.classEqRefl (syn_cwppcardt4fn)))
  have p0001 :=
    @g_wppcardt2fnexndv
  have p0002 :=
    @g_wppcardt2fnexndv
  have p0003 :=
    @g_siex (syn_cwppcardt2fn) p0002
  have p0004 :=
    @g_siex (syn_csi (syn_cwppcardt2fn)) p0003
  have p0005 :=
    @g_coex (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))) p0001 p0004
  have p0006 :=
    @g_eqeltri (syn_cwppcardt4fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_wppcardt4fnmapndv
     :
    Nominal.NPrf (syn_wf (syn_cwppcardt4fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_wppcardt2fnmapndv
  have p0001 :=
    @g_wppcardt2fnmapndv
  have p0002 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt2fn))
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) (syn_wf (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0000 p0005
  have p0007 :=
    @g_fco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    (by simpa [syn_cwppcardt4fn] using (Nominal.classEqRefl (syn_cwppcardt4fn)))
  have p0010 :=
    @g_feq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs) (syn_cwppcardt4fn) (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) p0009
  have p0011 :=
    @g_mpbir (syn_wf (syn_cwppcardt4fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)) (syn_wf (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)) p0008 p0010
  exact p0011

#print axioms g_wppcardt4fnmapndv

end NFChoice.DirectNominalPrf.WPPReplay
