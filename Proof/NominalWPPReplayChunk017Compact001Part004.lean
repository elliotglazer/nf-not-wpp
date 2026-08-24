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
import NominalWPPReplayChunk017Compact001Part003

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

noncomputable def g_sieqdndv
    (ph : Wff) (A : Class) (B : Class) (hyp_sieqdndv_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_csi A) (syn_csi B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have dv_cache_0001 : w ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0006 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0007 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0010 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_si x y z w A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_a1i (.classEq (syn_csi A) (syn_copab x y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) A (.cv w))))))) ph p0000
  have p0002 :=
    @g_breqd ph A B (.cv z) (.cv w) hyp_sieqdndv_1
  have p0003 :=
    @g_n_3anbi3d ph (syn_wbr (.cv z) A (.cv w)) (syn_wbr (.cv z) B (.cv w)) (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) p0002
  have p0004 :=
    @g_n_2exbidv ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) A (.cv w))) (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) B (.cv w))) z w dv_cache_0011 dv_cache_0012 p0003
  have p0005 :=
    @g_opabbidv ph (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) A (.cv w))))) (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) B (.cv w))))) x y dv_cache_0013 dv_cache_0014 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_si x y z w B dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0007 :=
    @g_eqcomi (syn_csi B) (syn_copab x y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) B (.cv w)))))) p0006
  have p0008 :=
    @g_a1i (.classEq (syn_copab x y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) B (.cv w)))))) (syn_csi B)) ph p0007
  have p0009 :=
    @g_n_3eqtrd ph (syn_csi A) (syn_copab x y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) A (.cv w)))))) (syn_copab x y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) B (.cv w)))))) (syn_csi B) p0001 p0005 p0008
  exact p0009

noncomputable def g_hnsicodemapvalclndv
    (A : Class) (Q : Class) :
    Nominal.NPrf (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) Q) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q)))))) := by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (Q).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) Q) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q))))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_Q, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex Q (syn_cpw1 (syn_chwcn A))
  have p0001 :=
    @g_id (.classEq (.cv q) Q)
  have p0002 :=
    @g_eleq1d (.classEq (.cv q) Q) (.cv q) Q (syn_cpw1 (syn_chwcn A)) p0001
  have p0003 :=
    @g_id (.classEq (.cv q) Q)
  have p0004 :=
    @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsicodemap A) p0003
  have p0005 :=
    @g_id (.classEq (.cv q) Q)
  have p0006 :=
    @g_unieqd (.classEq (.cv q) Q) (.cv q) Q p0005
  have p0007 :=
    @g_fveq2d (.classEq (.cv q) Q) (syn_cuni (.cv q)) (syn_cuni Q) (syn_c1st) p0006
  have p0008 :=
    @g_sieqdndv (.classEq (.cv q) Q) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni Q)) p0007
  have p0009 :=
    @g_id (.classEq (.cv q) Q)
  have p0010 :=
    @g_unieqd (.classEq (.cv q) Q) (.cv q) Q p0009
  have p0011 :=
    @g_fveq2d (.classEq (.cv q) Q) (syn_cuni (.cv q)) (syn_cuni Q) (syn_c2nd) p0010
  have p0012 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni Q))
  have p0013 :=
    @g_syl (.classEq (.cv q) Q) (.classEq (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni Q))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q)))) p0011 p0012
  have p0014 :=
    @g_opeq12d (.classEq (.cv q) Q) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q))) p0008 p0013
  have p0015 :=
    @g_eqeq12d (.classEq (.cv q) Q) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) Q) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q)))) p0004 p0014
  have p0016 :=
    @g_imbi12d (.classEq (.cv q) Q) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.classEq (syn_cfv (syn_chnsicodemap A) Q) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q))))) p0002 p0015
  have p0017 :=
    @g_hnsicodemapvalndv A q dv_cache_0001
  have p0018 :=
    @g_vtoclg (.imp (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))) (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) Q) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q)))))) q Q (syn_cvv) dv_cache_0002 dv_cache_0003 p0016 p0017
  have p0019 :=
    @g_mpcom (.classMem Q (syn_cvv)) (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) Q) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni Q))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni Q))))) p0000 p0018
  exact p0019

noncomputable def g_hnsicodemapfondv
    (A : Class) :
    Nominal.NPrf (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_u_ne_q : u ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_u : q ≠ u :=
    Ne.symm fresh_u_ne_q
  have fresh_u_ne_x : u ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_q_ne_x : q ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_y : q ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_q : y ≠ q :=
    Ne.symm fresh_q_ne_y
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ ((syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, fresh_q_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : q ∉ ((Wff.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_u, fresh_q_ne_x, fresh_q_ne_y, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((syn_chwcn (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : u ∉ ((syn_chwcn (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : q ∉ ((syn_chnsicodemap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : u ∉ ((syn_chnsicodemap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : q ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have p0000 :=
    @g_hnsicodemapfndv A
  have p0001 :=
    @g_hnsireversecodememndv x y u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_snelpw1 (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)
  have p0003 :=
    @g_a1i (syn_wb (.classMem (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0002
  have p0004 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)) p0001 p0003
  have p0005 :=
    @g_hnsireversecodeidndv x y u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0006 :=
    @g_hnsireversecodememndv x y u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0007 :=
    @g_snelpw1 (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)
  have p0008 :=
    @g_a1i (syn_wb (.classMem (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0007
  have p0009 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)) p0006 p0008
  have p0010 :=
    @g_hnsicodemapvalclndv A (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))
  have p0011 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))))) p0009 p0010
  have p0012 :=
    @g_hnsireversecodememndv x y u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0013 :=
    @g_elex (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)
  have p0014 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_unisng (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv)
  have p0016 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv)) (.classEq (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0014 p0015
  have p0017 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_c1st) p0016
  have p0018 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0019 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0007 dv_cache_0008 dv_cache_0006 p0018
  have p0020 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0021 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0020
  have p0022 :=
    @g_opfv1st (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0019 p0021
  have p0023 :=
    @g_a1i (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0022
  have p0024 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) (syn_cfv (syn_c1st) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) p0017 p0023
  have p0025 :=
    @g_sieqdndv (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) p0024
  have p0026 :=
    @g_hnsireversecodememndv x y u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0027 :=
    @g_elex (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)
  have p0028 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn A)) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv)) p0026 p0027
  have p0029 :=
    @g_unisng (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv)
  have p0030 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv)) (.classEq (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0028 p0029
  have p0031 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (syn_c2nd) p0030
  have p0032 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0033 :=
    @g_hndownexclndv x y (syn_cfv (syn_c1st) (.cv u)) dv_cache_0007 dv_cache_0008 dv_cache_0006 p0032
  have p0034 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0035 :=
    @g_uniex (syn_cfv (syn_c2nd) (.cv u)) p0034
  have p0036 :=
    @g_opfv2nd (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0033 p0035
  have p0037 :=
    @g_a1i (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) p0036
  have p0038 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) (syn_cfv (syn_c2nd) (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))) p0031 p0037
  have p0039 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))
  have p0040 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classEq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0038 p0039
  have p0041 :=
    @g_opeq12d (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))) p0025 p0040
  have p0042 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))))) (syn_cop (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0011 p0041
  have p0043 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cop (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) p0042
  have p0044 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.cv u) (syn_cop (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y))))) (syn_cpw1 (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) p0005 p0043
  have p0045 :=
    @g_jca (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) p0004 p0044
  have p0046 :=
    @g_id (.classEq (.cv q) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))
  have p0047 :=
    @g_fveq2d (.classEq (.cv q) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (.cv q) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_chnsicodemap A) p0046
  have p0048 :=
    @g_eqeq2d (.classEq (.cv q) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))) (.cv u) p0047
  have p0049 :=
    @g_rspcev (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q))) (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))))) q (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A)) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0048
  have p0050 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 A))) (syn_wa (.classMem (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (syn_csn (syn_cop (syn_copab x y (syn_wbr (syn_csn (.cv x)) (syn_cfv (syn_c1st) (.cv u)) (syn_csn (.cv y)))) (syn_cuni (syn_cfv (syn_c2nd) (.cv u)))))))) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q)))) p0045 p0049
  have p0051 :=
    @g_rgen (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q)))) u (syn_chwcn (syn_cpw1 A)) p0050
  have p0052 :=
    @g_pm3_2i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wral u (syn_chwcn (syn_cpw1 A)) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q))))) p0000 p0051
  have p0053 :=
    @g_dffo3 q u (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_chnsicodemap A) dv_cache_0010 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0054 :=
    @g_biimpri (syn_wfo (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (syn_wral u (syn_chwcn (syn_cpw1 A)) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv u) (syn_cfv (syn_chnsicodemap A) (.cv q)))))) p0053
  have p0055 :=
    Nominal.mp p0052 p0054
  exact p0055

noncomputable def g_siinjndv
    (ph : Wff) (R : Class) (S : Class) (hyp_siinjndv_1 : Nominal.NPrf (.imp ph (.classEq (syn_csi R) (syn_csi S)))) :
    Nominal.NPrf (.imp ph (.classEq R S)) := by
  let proofSupport : Finset Var := ph.fv ∪ R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (R).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_breqd ph (syn_csi R) (syn_csi S) (syn_csn (.cv x)) (syn_csn (.cv y)) hyp_siinjndv_1
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_vex y
  have p0003 :=
    @g_brsnsi (.cv x) (.cv y) R p0001 p0002
  have p0004 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) ph p0003
  have p0005 :=
    @g_bicomd ph (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)) p0004
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_vex y
  have p0008 :=
    @g_brsnsi (.cv x) (.cv y) S p0006 p0007
  have p0009 :=
    @g_a1i (syn_wb (syn_wbr (syn_csn (.cv x)) (syn_csi S) (syn_csn (.cv y))) (syn_wbr (.cv x) S (.cv y))) ph p0008
  have p0010 :=
    @g_bicomd ph (syn_wbr (syn_csn (.cv x)) (syn_csi S) (syn_csn (.cv y))) (syn_wbr (.cv x) S (.cv y)) p0009
  have p0011 :=
    @g_n_3bitr4d ph (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) (syn_csi S) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv y)) p0000 p0005 p0010
  have p0012 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) R (.cv y))))
  have p0013 :=
    @g_bicomi (syn_wbr (.cv x) R (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) R) p0012
  have p0014 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) R) (syn_wbr (.cv x) R (.cv y))) ph p0013
  have p0015 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) S (.cv y))))
  have p0016 :=
    @g_bicomi (syn_wbr (.cv x) S (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) S) p0015
  have p0017 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) S) (syn_wbr (.cv x) S (.cv y))) ph p0016
  have p0018 :=
    @g_n_3bitr4d ph (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) R) (.classMem (syn_cop (.cv x) (.cv y)) S) p0011 p0014 p0017
  have p0019 :=
    @g_eqrelrdv ph x y R S dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0018
  exact p0019

noncomputable def g_hwcnpairclndv
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_chwcn A)) (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Wff.imp (.classMem B (syn_chwcn A)) (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex B (syn_chwcn A)
  have p0001 :=
    @g_id (.classEq (.cv u) B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0001
  have p0003 :=
    @g_id (.classEq (.cv u) B)
  have p0004 :=
    @g_id (.classEq (.cv u) B)
  have p0005 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c1st) p0004
  have p0006 :=
    @g_id (.classEq (.cv u) B)
  have p0007 :=
    @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0006
  have p0008 :=
    @g_opeq12d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B) p0005 p0007
  have p0009 :=
    @g_eqeq12d (.classEq (.cv u) B) (.cv u) B (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)) p0003 p0008
  have p0010 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))) p0002 p0009
  have p0011 :=
    @g_hwcnpair u A
  have p0012 :=
    @g_vtoclg (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (.imp (.classMem B (syn_chwcn A)) (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) u B (syn_cvv) dv_cache_0001 dv_cache_0002 p0010 p0011
  have p0013 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B (syn_chwcn A)) (.classEq B (syn_cop (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))) p0000 p0012
  exact p0013

#print axioms g_hwcnpairclndv

end NFChoice.DirectNominalPrf.WPPReplay
