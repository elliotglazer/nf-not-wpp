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
import NominalWPPReplayChunk012BCompact001Part016

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

noncomputable def g_ovmpt2
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (F : Class) (G : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_G_x : x ∉ G.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y) (hyp_ovmpt2g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq R G))) (hyp_ovmpt2g_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (.classEq G S))) (hyp_ovmpt2g_3 : Nominal.NPrf (.classEq F (syn_cmpt2 x C y D R))) (hyp_ovmpt2_4 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.classMem B D)) (.classEq (syn_co A F B) S)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ F.fv ∪ G.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_ovmpt2g x y A B C D R S F G (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_ovmpt2g_1 hyp_ovmpt2g_2 hyp_ovmpt2g_3
  have p0001 :=
    @g_mp3an3 (.classMem A C) (.classMem B D) (.classMem S (syn_cvv)) (.classEq (syn_co A F B) S) hyp_ovmpt2_4 p0000
  exact p0001

noncomputable def g_mptv
    (x : Var) (y : Var) (B : Class) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cmpt x (syn_cvv) B) (syn_copab x y (.classEq (.cv y) B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ B.fv
  have dv_cache_0001 : y ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y (syn_cvv) B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_biantrur (.classMem (.cv x) (syn_cvv)) (.classEq (.cv y) B) p0001
  have p0003 :=
    @g_opabbii (.classEq (.cv y) B) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classEq (.cv y) B)) x y p0002
  have p0004 :=
    @g_eqtr4i (syn_cmpt x (syn_cvv) B) (syn_copab x y (syn_wa (.classMem (.cv x) (syn_cvv)) (.classEq (.cv y) B))) (syn_copab x y (.classEq (.cv y) B)) p0000 p0003
  exact p0004

noncomputable def g_f1od
    (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (W : Class) (X : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y) (hyp_f1od_1 : Nominal.NPrf (.classEq F (syn_cmpt x A C))) (hyp_f1od_2 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.classMem C W))) (hyp_f1od_3 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv y) B)) (.classMem D X))) (hyp_f1od_4 : Nominal.NPrf (.imp ph (syn_wb (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C)) (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D))))) :
    Nominal.NPrf (.imp ph (syn_wf1o F A B)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv ∪ W.fv ∪ X.fv
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 :=
    @g_ralrimiva ph (.classMem C W) x A dv_cache_0001 hyp_f1od_2
  have p0001 :=
    @g_fnmpt x A C F W dv_cache_0002 hyp_f1od_1
  have p0002 :=
    @g_syl ph (syn_wral x A (.classMem C W)) (syn_wfn F A) p0000 p0001
  have p0003 :=
    @g_ralrimiva ph (.classMem D X) y B dv_cache_0003 hyp_f1od_3
  have p0004 :=
    @g_eqid (syn_cmpt y B D)
  have p0005 :=
    @g_fnmpt y B D (syn_cmpt y B D) X dv_cache_0004 p0004
  have p0006 :=
    @g_syl ph (syn_wral y B (.classMem D X)) (syn_wfn (syn_cmpt y B D) B) p0003 p0005
  have p0007 :=
    @g_opabbidv ph (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C)) (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D)) y x dv_cache_0003 dv_cache_0001 hyp_f1od_4
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A C dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0009 :=
    @g_eqtri F (syn_cmpt x A C) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) hyp_f1od_1 p0008
  have p0010 :=
    @g_cnveqi F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) p0009
  have p0011 :=
    @g_cnvopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C)) x y dv_cache_0007
  have p0012 :=
    @g_eqtri (syn_ccnv F) (syn_ccnv (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C)))) (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) p0010 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt y x B D dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0014 :=
    @g_n_3eqtr4g ph (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) (syn_copab y x (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D))) (syn_ccnv F) (syn_cmpt y B D) p0007 p0012 p0013
  have p0015 :=
    @g_fneq1d ph B (syn_ccnv F) (syn_cmpt y B D) p0014
  have p0016 :=
    @g_mpbird ph (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_cmpt y B D) B) p0006 p0015
  have p0017 :=
    @g_dff1o4 A B F
  have p0018 :=
    @g_sylanbrc ph (syn_wfn F A) (syn_wfn (syn_ccnv F) B) (syn_wf1o F A B) p0002 p0016 p0017
  exact p0018

noncomputable def g_f1o2d
    (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y) (hyp_f1od_1 : Nominal.NPrf (.classEq F (syn_cmpt x A C))) (hyp_f1o2d_2 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.classMem C B))) (hyp_f1o2d_3 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv y) B)) (.classMem D A))) (hyp_f1o2d_4 : Nominal.NPrf (.imp (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (syn_wb (.classEq (.cv x) D) (.classEq (.cv y) C)))) :
    Nominal.NPrf (.imp ph (syn_wf1o F A B)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_eleq1a C B (.cv y)
  have p0001 :=
    @g_syl (syn_wa ph (.classMem (.cv x) A)) (.classMem C B) (.imp (.classEq (.cv y) C) (.classMem (.cv y) B)) hyp_f1o2d_2 p0000
  have p0002 :=
    @g_impr ph (.classMem (.cv x) A) (.classEq (.cv y) C) (.classMem (.cv y) B) p0001
  have p0003 :=
    @g_biimpar (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.classEq (.cv x) D) (.classEq (.cv y) C) hyp_f1o2d_4
  have p0004 :=
    @g_exp42 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.classEq (.cv y) C) (.classEq (.cv x) D) p0003
  have p0005 :=
    @g_com34 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.classEq (.cv y) C) (.classEq (.cv x) D) p0004
  have p0006 :=
    @g_imp32 ph (.classMem (.cv x) A) (.classEq (.cv y) C) (.imp (.classMem (.cv y) B) (.classEq (.cv x) D)) p0005
  have p0007 :=
    @g_jcai (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) (.classMem (.cv y) B) (.classEq (.cv x) D) p0002 p0006
  have p0008 :=
    @g_eleq1a D A (.cv x)
  have p0009 :=
    @g_syl (syn_wa ph (.classMem (.cv y) B)) (.classMem D A) (.imp (.classEq (.cv x) D) (.classMem (.cv x) A)) hyp_f1o2d_3 p0008
  have p0010 :=
    @g_impr ph (.classMem (.cv y) B) (.classEq (.cv x) D) (.classMem (.cv x) A) p0009
  have p0011 :=
    @g_biimpa (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.classEq (.cv x) D) (.classEq (.cv y) C) hyp_f1o2d_4
  have p0012 :=
    @g_exp42 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.classEq (.cv x) D) (.classEq (.cv y) C) p0011
  have p0013 :=
    @g_com23 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.imp (.classEq (.cv x) D) (.classEq (.cv y) C)) p0012
  have p0014 :=
    @g_com34 ph (.classMem (.cv y) B) (.classMem (.cv x) A) (.classEq (.cv x) D) (.classEq (.cv y) C) p0013
  have p0015 :=
    @g_imp32 ph (.classMem (.cv y) B) (.classEq (.cv x) D) (.imp (.classMem (.cv x) A) (.classEq (.cv y) C)) p0014
  have p0016 :=
    @g_jcai (syn_wa ph (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D))) (.classMem (.cv x) A) (.classEq (.cv y) C) p0010 p0015
  have p0017 :=
    @g_impbida ph (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C)) (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D)) p0007 p0016
  have p0018 :=
    @g_f1od ph x y A B C D F B A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_f1od_1 hyp_f1o2d_2 hyp_f1o2d_3 p0017
  exact p0018

#print axioms g_f1o2d

end NFChoice.DirectNominalPrf.WPPReplay
