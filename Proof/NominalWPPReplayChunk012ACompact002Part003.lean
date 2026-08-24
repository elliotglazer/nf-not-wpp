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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk012ACompact002Part002

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

noncomputable def g_funbrfv
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (.imp (syn_wbr A F B) (.classEq (syn_cfv F A) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_funeu y A B F dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_tz6_12_1 y A B F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_sylan2 (syn_wa (syn_wfun F) (syn_wbr A F B)) (syn_wbr A F B) (syn_weu y (syn_wbr A F (.cv y))) (.classEq (syn_cfv F A) B) p0000 p0001
  have p0003 :=
    @g_anabss7 (syn_wfun F) (syn_wbr A F B) (.classEq (syn_cfv F A) B) p0002
  have p0004 :=
    @g_ex (syn_wfun F) (syn_wbr A F B) (.classEq (syn_cfv F A) B) p0003
  exact p0004

noncomputable def g_funopfv
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (.imp (.classMem (syn_cop A B) F) (.classEq (syn_cfv F A) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A F B)))
  have p0001 :=
    @g_funbrfv A B F
  have p0002 :=
    @g_syl5bir (.classMem (syn_cop A B) F) (syn_wbr A F B) (syn_wfun F) (.classEq (syn_cfv F A) B) p0000 p0001
  exact p0002

noncomputable def g_fnbrfvb
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem B A)) (syn_wb (.classEq (syn_cfv F B) C) (syn_wbr B F C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fneu x A B F dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_tz6_12c x B C F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_syl (syn_wa (syn_wfn F A) (.classMem B A)) (syn_weu x (syn_wbr B F (.cv x))) (syn_wb (.classEq (syn_cfv F B) C) (syn_wbr B F C)) p0000 p0001
  exact p0002

noncomputable def g_fnopfvb
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem B A)) (syn_wb (.classEq (syn_cfv F B) C) (.classMem (syn_cop B C) F))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_fnbrfvb A B C F
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr B F C)))
  have p0002 :=
    @g_syl6bb (syn_wa (syn_wfn F A) (.classMem B A)) (.classEq (syn_cfv F B) C) (syn_wbr B F C) (.classMem (syn_cop B C) F) p0000 p0001
  exact p0002

noncomputable def g_funbrfvb
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (syn_wb (.classEq (syn_cfv F A) B) (syn_wbr A F B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_funfn F
  have p0001 :=
    @g_fnbrfvb (syn_cdm F) A B F
  have p0002 :=
    @g_sylanb (syn_wfun F) (syn_wfn F (syn_cdm F)) (.classMem A (syn_cdm F)) (syn_wb (.classEq (syn_cfv F A) B) (syn_wbr A F B)) p0000 p0001
  exact p0002

noncomputable def g_funopfvb
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (syn_wb (.classEq (syn_cfv F A) B) (.classMem (syn_cop A B) F))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_funbrfvb A B F
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A F B)))
  have p0002 :=
    @g_syl6bb (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classEq (syn_cfv F A) B) (syn_wbr A F B) (.classMem (syn_cop A B) F) p0000 p0001
  exact p0002

noncomputable def g_funbrfv2b
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wb (syn_wbr A F B) (syn_wa (.classMem A (syn_cdm F)) (.classEq (syn_cfv F A) B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_breldm A B F
  have p0001 :=
    @g_a1i (.imp (syn_wbr A F B) (.classMem A (syn_cdm F))) (syn_wfun F) p0000
  have p0002 :=
    @g_pm4_71rd (syn_wfun F) (syn_wbr A F B) (.classMem A (syn_cdm F)) p0001
  have p0003 :=
    @g_funbrfvb A B F
  have p0004 :=
    @g_pm5_32da (syn_wfun F) (.classMem A (syn_cdm F)) (.classEq (syn_cfv F A) B) (syn_wbr A F B) p0003
  have p0005 :=
    @g_bitr4d (syn_wfun F) (syn_wbr A F B) (syn_wa (.classMem A (syn_cdm F)) (syn_wbr A F B)) (syn_wa (.classMem A (syn_cdm F)) (.classEq (syn_cfv F A) B)) p0002 p0004
  exact p0005

noncomputable def g_fnrnfv
    (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wfn F A) (.classEq (syn_crn F) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ F.fv
  have dv_cache_0001 : x ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0004 : x ∉ ((syn_wfn F A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_wfn F A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dfrn3 x y F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_fnop A (.cv x) (.cv y) F
  have p0002 :=
    @g_ex (syn_wfn F A) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) A) p0001
  have p0003 :=
    @g_pm4_71rd (syn_wfn F A) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_fnopfvb A (.cv x) (.cv y) F
  have p0005 :=
    @g_pm5_32da (syn_wfn F A) (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) F) p0004
  have p0006 :=
    @g_bitr4d (syn_wfn F A) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) F)) (syn_wa (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y))) p0003 p0005
  have p0007 :=
    @g_exbidv (syn_wfn F A) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wa (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y))) x dv_cache_0004 p0006
  have p0008 :=
    @g_eqcom (.cv y) (syn_cfv F (.cv x))
  have p0009 :=
    @g_rexbii (.classEq (.cv y) (syn_cfv F (.cv x))) (.classEq (syn_cfv F (.cv x)) (.cv y)) x A p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y)))))
  have p0011 :=
    @g_bitri (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y))) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y)))) p0009 p0010
  have p0012 :=
    @g_syl6bbr (syn_wfn F A) (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) F)) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y)))) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) p0007 p0011
  have p0013 :=
    @g_abbidv (syn_wfn F A) (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) F)) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) y dv_cache_0005 p0012
  have p0014 :=
    @g_syl5eq (syn_wfn F A) (syn_crn F) (.cab y (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) F))) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0000 p0013
  exact p0014

noncomputable def g_fvelrnb
    (x : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wfn F A) (syn_wb (.classMem B (syn_crn F)) (syn_wrex x A (.classEq (syn_cfv F (.cv x)) B)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ ((Wff.classMem B (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_wrex x A (.classEq (syn_cfv F (.cv x)) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, fresh_y_not_F, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fnrnfv x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eleq2d (syn_wfn F A) (syn_crn F) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B p0000
  have p0002 :=
    @g_fvex (.cv x) F
  have p0003 :=
    @g_eleq1 (syn_cfv F (.cv x)) B (syn_cvv)
  have p0004 :=
    @g_mpbii (.classEq (syn_cfv F (.cv x)) B) (.classMem (syn_cfv F (.cv x)) (syn_cvv)) (.classMem B (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_rexlimivw (.classEq (syn_cfv F (.cv x)) B) (.classMem B (syn_cvv)) x A dv_cache_0006 p0004
  have p0006 :=
    @g_eqeq1 (.cv y) B (syn_cfv F (.cv x))
  have p0007 :=
    @g_eqcom B (syn_cfv F (.cv x))
  have p0008 :=
    @g_syl6bb (.classEq (.cv y) B) (.classEq (.cv y) (syn_cfv F (.cv x))) (.classEq B (syn_cfv F (.cv x))) (.classEq (syn_cfv F (.cv x)) B) p0006 p0007
  have p0009 :=
    @g_rexbidv (.classEq (.cv y) B) (.classEq (.cv y) (syn_cfv F (.cv x))) (.classEq (syn_cfv F (.cv x)) B) x A dv_cache_0007 p0008
  have p0010 :=
    @g_elab3 (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (syn_wrex x A (.classEq (syn_cfv F (.cv x)) B)) y B dv_cache_0008 dv_cache_0009 p0005 p0009
  have p0011 :=
    @g_syl6bb (syn_wfn F A) (.classMem B (syn_crn F)) (.classMem B (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))))) (syn_wrex x A (.classEq (syn_cfv F (.cv x)) B)) p0001 p0010
  exact p0011

noncomputable def g_dfimafn
    (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.classEq (syn_cima F A) (.cab y (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ F.fv
  have dv_cache_0001 : x ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 :=
    @g_ssel2 A (syn_cdm F) (.cv x)
  have p0001 :=
    @g_funbrfvb (.cv x) (.cv y) F
  have p0002 :=
    @g_sylan2 (syn_wa (syn_wss A (syn_cdm F)) (.classMem (.cv x) A)) (syn_wfun F) (.classMem (.cv x) (syn_cdm F)) (syn_wb (.classEq (syn_cfv F (.cv x)) (.cv y)) (syn_wbr (.cv x) F (.cv y))) p0000 p0001
  have p0003 :=
    @g_anassrs (syn_wfun F) (syn_wss A (syn_cdm F)) (.classMem (.cv x) A) (syn_wb (.classEq (syn_cfv F (.cv x)) (.cv y)) (syn_wbr (.cv x) F (.cv y))) p0002
  have p0004 :=
    @g_rexbidva (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.classEq (syn_cfv F (.cv x)) (.cv y)) (syn_wbr (.cv x) F (.cv y)) x A dv_cache_0001 p0003
  have p0005 :=
    @g_abbidv (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y))) (syn_wrex x A (syn_wbr (.cv x) F (.cv y))) y dv_cache_0002 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x F A dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @g_syl6reqr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.cab y (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y)))) (.cab y (syn_wrex x A (syn_wbr (.cv x) F (.cv y)))) (syn_cima F A) p0005 p0006
  exact p0007

noncomputable def g_funimass4
    (x : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wb (syn_wss (syn_cima F A) B) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((syn_cima F A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : y ∉ ((syn_cfv F (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classMem (syn_cfv F (.cv x)) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dfss2 y (syn_cima F A) B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_ssel2 A (syn_cdm F) (.cv x)
  have p0002 :=
    @g_eqcom (.cv y) (syn_cfv F (.cv x))
  have p0003 :=
    @g_funbrfvb (.cv x) (.cv y) F
  have p0004 :=
    @g_syl5bb (.classEq (.cv y) (syn_cfv F (.cv x))) (.classEq (syn_cfv F (.cv x)) (.cv y)) (syn_wa (syn_wfun F) (.classMem (.cv x) (syn_cdm F))) (syn_wbr (.cv x) F (.cv y)) p0002 p0003
  have p0005 :=
    @g_sylan2 (syn_wa (syn_wss A (syn_cdm F)) (.classMem (.cv x) A)) (syn_wfun F) (.classMem (.cv x) (syn_cdm F)) (syn_wb (.classEq (.cv y) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (.cv y))) p0001 p0004
  have p0006 :=
    @g_anassrs (syn_wfun F) (syn_wss A (syn_cdm F)) (.classMem (.cv x) A) (syn_wb (.classEq (.cv y) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (.cv y))) p0005
  have p0007 :=
    @g_rexbidva (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.classEq (.cv y) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (.cv y)) x A dv_cache_0003 p0006
  have p0008 :=
    @g_elima x (.cv y) F A dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0009 :=
    @g_syl6rbbr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (syn_wrex x A (syn_wbr (.cv x) F (.cv y))) (.classMem (.cv y) (syn_cima F A)) p0007 p0008
  have p0010 :=
    @g_imbi1d (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.classMem (.cv y) (syn_cima F A)) (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B) p0009
  have p0011 :=
    @g_r19_23v (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B) x A dv_cache_0007
  have p0012 :=
    @g_syl6bbr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.imp (.classMem (.cv y) (syn_cima F A)) (.classMem (.cv y) B)) (.imp (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B)) (syn_wral x A (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B))) p0010 p0011
  have p0013 :=
    @g_albidv (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.imp (.classMem (.cv y) (syn_cima F A)) (.classMem (.cv y) B)) (syn_wral x A (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B))) y dv_cache_0008 p0012
  have p0014 :=
    @g_ralcom4 (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B)) x y A dv_cache_0009 dv_cache_0010
  have p0015 :=
    @g_fvex (.cv x) F
  have p0016 :=
    @g_eleq1 (.cv y) (syn_cfv F (.cv x)) B
  have p0017 :=
    @g_ceqsalv (.classMem (.cv y) B) (.classMem (syn_cfv F (.cv x)) B) y (syn_cfv F (.cv x)) dv_cache_0011 dv_cache_0012 p0015 p0016
  have p0018 :=
    @g_ralbii (.all y (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B))) (.classMem (syn_cfv F (.cv x)) B) x A p0017
  have p0019 :=
    @g_bitr3i (.all y (syn_wral x A (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B)))) (syn_wral x A (.all y (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B)))) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) p0014 p0018
  have p0020 :=
    @g_syl6bb (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.all y (.imp (.classMem (.cv y) (syn_cima F A)) (.classMem (.cv y) B))) (.all y (syn_wral x A (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B)))) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) p0013 p0019
  have p0021 :=
    @g_syl5bb (syn_wss (syn_cima F A) B) (.all y (.imp (.classMem (.cv y) (syn_cima F A)) (.classMem (.cv y) B))) (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) p0000 p0020
  exact p0021

noncomputable def g_fvelima
    (x : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cima F B))) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) A))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elima x A F B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_funbrfv (.cv x) A F
  have p0002 :=
    @g_reximdv (syn_wfun F) (syn_wbr (.cv x) F A) (.classEq (syn_cfv F (.cv x)) A) x B dv_cache_0004 p0001
  have p0003 :=
    @g_syl5bi (.classMem A (syn_cima F B)) (syn_wrex x B (syn_wbr (.cv x) F A)) (syn_wfun F) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) A)) p0000 p0002
  have p0004 :=
    @g_imp (syn_wfun F) (.classMem A (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) A)) p0003
  exact p0004

noncomputable def g_fvelimab
    (x : Var) (A : Class) (B : Class) (C : Class) (F : Class) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wb (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classMem C (syn_cvv))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wb (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex C (syn_cima F B)
  have p0001 :=
    @g_anim2i (.classMem C (syn_cima F B)) (.classMem C (syn_cvv)) (syn_wa (syn_wfn F A) (syn_wss B A)) p0000
  have p0002 :=
    @g_fvex (.cv x) F
  have p0003 :=
    @g_eleq1 (syn_cfv F (.cv x)) C (syn_cvv)
  have p0004 :=
    @g_mpbii (.classEq (syn_cfv F (.cv x)) C) (.classMem (syn_cfv F (.cv x)) (syn_cvv)) (.classMem C (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_rexlimivw (.classEq (syn_cfv F (.cv x)) C) (.classMem C (syn_cvv)) x B dv_cache_0001 p0004
  have p0006 :=
    @g_anim2i (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)) (.classMem C (syn_cvv)) (syn_wa (syn_wfn F A) (syn_wss B A)) p0005
  have p0007 :=
    @g_eleq1 (.cv y) C (syn_cima F B)
  have p0008 :=
    @g_eqeq2 (.cv y) C (syn_cfv F (.cv x))
  have p0009 :=
    @g_rexbidv (.classEq (.cv y) C) (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classEq (syn_cfv F (.cv x)) C) x B dv_cache_0002 p0008
  have p0010 :=
    @g_bibi12d (.classEq (.cv y) C) (.classMem (.cv y) (syn_cima F B)) (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y))) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)) p0007 p0009
  have p0011 :=
    @g_imbi2d (.classEq (.cv y) C) (syn_wb (.classMem (.cv y) (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y)))) (syn_wb (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C))) (syn_wa (syn_wfn F A) (syn_wss B A)) p0010
  have p0012 :=
    @g_fnfun A F
  have p0013 :=
    @g_adantr (syn_wfn F A) (syn_wfun F) (syn_wss B A) p0012
  have p0014 :=
    @g_fndm A F
  have p0015 :=
    @g_sseq2d (syn_wfn F A) (syn_cdm F) A B p0014
  have p0016 :=
    @g_biimpar (syn_wfn F A) (syn_wss B (syn_cdm F)) (syn_wss B A) p0015
  have p0017 :=
    @g_dfimafn x y B F dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0018 :=
    @g_syl2anc (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wfun F) (syn_wss B (syn_cdm F)) (.classEq (syn_cima F B) (.cab y (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y))))) p0013 p0016 p0017
  have p0019 :=
    @g_eqabrd (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y))) y (syn_cima F B) p0018
  have p0020 :=
    @g_vtoclg (.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wb (.classMem (.cv y) (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y))))) (.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wb (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)))) y C (syn_cvv) dv_cache_0008 dv_cache_0009 p0011 p0019
  have p0021 :=
    @g_impcom (.classMem C (syn_cvv)) (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wb (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C))) p0020
  have p0022 :=
    @g_pm5_21nd (syn_wa (syn_wfn F A) (syn_wss B A)) (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)) (syn_wa (syn_wa (syn_wfn F A) (syn_wss B A)) (.classMem C (syn_cvv))) p0001 p0006 p0021
  exact p0022

noncomputable def g_fnsnfv
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem B A)) (.classEq (syn_csn (syn_cfv F B)) (syn_cima F (syn_csn B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((syn_wa (syn_wfn F A) (.classMem B A))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cfv F B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqcom (.cv y) (syn_cfv F B)
  have p0001 :=
    @g_fnbrfvb A B (.cv y) F
  have p0002 :=
    @g_syl5bb (.classEq (.cv y) (syn_cfv F B)) (.classEq (syn_cfv F B) (.cv y)) (syn_wa (syn_wfn F A) (.classMem B A)) (syn_wbr B F (.cv y)) p0000 p0001
  have p0003 :=
    @g_abbidv (syn_wa (syn_wfn F A) (.classMem B A)) (.classEq (.cv y) (syn_cfv F B)) (syn_wbr B F (.cv y)) y dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn y (syn_cfv F B) dv_cache_0002
  have p0005 :=
    @g_imasn y B F dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_n_3eqtr4g (syn_wa (syn_wfn F A) (.classMem B A)) (.cab y (.classEq (.cv y) (syn_cfv F B))) (.cab y (syn_wbr B F (.cv y))) (syn_csn (syn_cfv F B)) (syn_cima F (syn_csn B)) p0003 p0004 p0005
  exact p0006

noncomputable def g_funfv
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (.classEq (syn_cfv F A) (syn_cuni (syn_cima F (syn_csn A))))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_fvex A F
  have p0001 :=
    @g_unisn (syn_cfv F A) p0000
  have p0002 :=
    @g_eqid (syn_cdm F)
  have p0003 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn F (syn_cdm F))))
  have p0004 :=
    @g_mpbiran2 (syn_wfn F (syn_cdm F)) (syn_wfun F) (.classEq (syn_cdm F) (syn_cdm F)) p0002 p0003
  have p0005 :=
    @g_fnsnfv (syn_cdm F) A F
  have p0006 :=
    @g_sylanbr (syn_wfun F) (syn_wfn F (syn_cdm F)) (.classMem A (syn_cdm F)) (.classEq (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A))) p0004 p0005
  have p0007 :=
    @g_unieqd (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A)) p0006
  have p0008 :=
    @g_syl5eqr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (syn_cfv F A) (syn_cuni (syn_csn (syn_cfv F A))) (syn_cuni (syn_cima F (syn_csn A))) p0001 p0007
  have p0009 :=
    @g_ex (syn_wfun F) (.classMem A (syn_cdm F)) (.classEq (syn_cfv F A) (syn_cuni (syn_cima F (syn_csn A)))) p0008
  have p0010 :=
    @g_ndmfv A F
  have p0011 :=
    @g_ndmima A F
  have p0012 :=
    @g_unieqd (.neg (.classMem A (syn_cdm F))) (syn_cima F (syn_csn A)) (syn_c0) p0011
  have p0013 :=
    @g_uni0
  have p0014 :=
    @g_syl6eq (.neg (.classMem A (syn_cdm F))) (syn_cuni (syn_cima F (syn_csn A))) (syn_cuni (syn_c0)) (syn_c0) p0012 p0013
  have p0015 :=
    @g_eqtr4d (.neg (.classMem A (syn_cdm F))) (syn_cfv F A) (syn_c0) (syn_cuni (syn_cima F (syn_csn A))) p0010 p0014
  have p0016 :=
    @g_pm2_61d1 (syn_wfun F) (.classMem A (syn_cdm F)) (.classEq (syn_cfv F A) (syn_cuni (syn_cima F (syn_csn A)))) p0009 p0015
  exact p0016

noncomputable def g_fvun
    (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (.classEq (syn_cfv (syn_cun F G) A) (syn_cun (syn_cfv F A) (syn_cfv G A)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_funun F G
  have p0001 :=
    @g_funfv A (syn_cun F G)
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (syn_wfun (syn_cun F G)) (.classEq (syn_cfv (syn_cun F G) A) (syn_cuni (syn_cima (syn_cun F G) (syn_csn A)))) p0000 p0001
  have p0003 :=
    @g_imaundir F G (syn_csn A)
  have p0004 :=
    @g_a1i (.classEq (syn_cima (syn_cun F G) (syn_csn A)) (syn_cun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A)))) (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) p0003
  have p0005 :=
    @g_unieqd (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (syn_cima (syn_cun F G) (syn_csn A)) (syn_cun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A))) p0004
  have p0006 :=
    @g_uniun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A))
  have p0007 :=
    @g_funfv A F
  have p0008 :=
    @g_eqcomd (syn_wfun F) (syn_cfv F A) (syn_cuni (syn_cima F (syn_csn A))) p0007
  have p0009 :=
    @g_funfv A G
  have p0010 :=
    @g_eqcomd (syn_wfun G) (syn_cfv G A) (syn_cuni (syn_cima G (syn_csn A))) p0009
  have p0011 :=
    @g_anim12i (syn_wfun F) (.classEq (syn_cuni (syn_cima F (syn_csn A))) (syn_cfv F A)) (syn_wfun G) (.classEq (syn_cuni (syn_cima G (syn_csn A))) (syn_cfv G A)) p0008 p0010
  have p0012 :=
    @g_adantr (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wa (.classEq (syn_cuni (syn_cima F (syn_csn A))) (syn_cfv F A)) (.classEq (syn_cuni (syn_cima G (syn_csn A))) (syn_cfv G A))) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) p0011
  have p0013 :=
    @g_uneq12 (syn_cuni (syn_cima F (syn_csn A))) (syn_cfv F A) (syn_cuni (syn_cima G (syn_csn A))) (syn_cfv G A)
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (syn_wa (.classEq (syn_cuni (syn_cima F (syn_csn A))) (syn_cfv F A)) (.classEq (syn_cuni (syn_cima G (syn_csn A))) (syn_cfv G A))) (.classEq (syn_cun (syn_cuni (syn_cima F (syn_csn A))) (syn_cuni (syn_cima G (syn_csn A)))) (syn_cun (syn_cfv F A) (syn_cfv G A))) p0012 p0013
  have p0015 :=
    @g_syl5eq (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (syn_cuni (syn_cun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A)))) (syn_cun (syn_cuni (syn_cima F (syn_csn A))) (syn_cuni (syn_cima G (syn_csn A)))) (syn_cun (syn_cfv F A) (syn_cfv G A)) p0006 p0014
  have p0016 :=
    @g_n_3eqtrd (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (syn_cfv (syn_cun F G) A) (syn_cuni (syn_cima (syn_cun F G) (syn_csn A))) (syn_cuni (syn_cun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A)))) (syn_cun (syn_cfv F A) (syn_cfv G A)) p0002 p0005 p0015
  exact p0016

#print axioms g_fvun

end NFChoice.DirectNominalPrf.WPPReplay
