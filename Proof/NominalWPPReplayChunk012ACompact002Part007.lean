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
import NominalWPPReplayChunk012ACompact002Part006

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

noncomputable def g_dff13
    (x : Var) (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0004 : z ∉ ((syn_wfn F A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Wff.objEq x y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cfv F (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_cfv F (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_wfn F A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_wfn F A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_wbr (.cv x) F (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_wbr (.cv y) F (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, fresh_x_ne_z, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dff12 x z A B F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_ffn A B F
  have p0002 :=
    @g_breldm (.cv x) (.cv z) F
  have p0003 :=
    @g_fndm A F
  have p0004 :=
    @g_eleq2d (syn_wfn F A) (syn_cdm F) A (.cv x) p0003
  have p0005 :=
    @g_syl5ib (syn_wbr (.cv x) F (.cv z)) (.classMem (.cv x) (syn_cdm F)) (syn_wfn F A) (.classMem (.cv x) A) p0002 p0004
  have p0006 :=
    @g_breldm (.cv y) (.cv z) F
  have p0007 :=
    @g_eleq2d (syn_wfn F A) (syn_cdm F) A (.cv y) p0003
  have p0008 :=
    @g_syl5ib (syn_wbr (.cv y) F (.cv z)) (.classMem (.cv y) (syn_cdm F)) (syn_wfn F A) (.classMem (.cv y) A) p0006 p0007
  have p0009 :=
    @g_anim12d (syn_wfn F A) (syn_wbr (.cv x) F (.cv z)) (.classMem (.cv x) A) (syn_wbr (.cv y) F (.cv z)) (.classMem (.cv y) A) p0005 p0008
  have p0010 :=
    @g_pm4_71rd (syn_wfn F A) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) p0009
  have p0011 :=
    @g_eqcom (.cv z) (syn_cfv F (.cv x))
  have p0012 :=
    @g_fnbrfvb A (.cv x) (.cv z) F
  have p0013 :=
    @g_syl5bb (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (syn_cfv F (.cv x)) (.cv z)) (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (syn_wbr (.cv x) F (.cv z)) p0011 p0012
  have p0014 :=
    @g_eqcom (.cv z) (syn_cfv F (.cv y))
  have p0015 :=
    @g_fnbrfvb A (.cv y) (.cv z) F
  have p0016 :=
    @g_syl5bb (.classEq (.cv z) (syn_cfv F (.cv y))) (.classEq (syn_cfv F (.cv y)) (.cv z)) (syn_wa (syn_wfn F A) (.classMem (.cv y) A)) (syn_wbr (.cv y) F (.cv z)) p0014 p0015
  have p0017 :=
    @g_bi2anan9 (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (.classEq (.cv z) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (.cv z)) (syn_wa (syn_wfn F A) (.classMem (.cv y) A)) (.classEq (.cv z) (syn_cfv F (.cv y))) (syn_wbr (.cv y) F (.cv z)) p0013 p0016
  have p0018 :=
    @g_anandis (syn_wfn F A) (.classMem (.cv x) A) (.classMem (.cv y) A) (syn_wb (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))) p0017
  have p0019 :=
    @g_pm5_32da (syn_wfn F A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) p0018
  have p0020 :=
    @g_bitr4d (syn_wfn F A) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))) p0010 p0019
  have p0021 :=
    @g_imbi1d (syn_wfn F A) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))) (.objEq x y) p0020
  have p0022 :=
    @g_impexp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y)
  have p0023 :=
    @g_syl6bb (syn_wfn F A) (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y)) (.imp (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))) (.objEq x y)) (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y))) p0021 p0022
  have p0024 :=
    @g_albidv (syn_wfn F A) (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y)) (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y))) z dv_cache_0004 p0023
  have p0025 :=
    @g_n_19_21v (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y)) z dv_cache_0005
  have p0026 :=
    @g_n_19_23v (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y) z dv_cache_0006
  have p0027 :=
    @g_fvex (.cv x) F
  have p0028 :=
    @g_eqvinc z (syn_cfv F (.cv x)) (syn_cfv F (.cv y)) dv_cache_0007 dv_cache_0008 p0027
  have p0029 :=
    @g_imbi1i (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))) (.objEq x y) p0028
  have p0030 :=
    @g_bitr4i (.all z (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y))) (.imp (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y))))) (.objEq x y)) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)) p0026 p0029
  have p0031 :=
    @g_imbi2i (.all z (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y))) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) p0030
  have p0032 :=
    @g_bitri (.all z (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y)))) (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.all z (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y)))) (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y))) p0025 p0031
  have p0033 :=
    @g_syl6bb (syn_wfn F A) (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))) (.all z (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (syn_wa (.classEq (.cv z) (syn_cfv F (.cv x))) (.classEq (.cv z) (syn_cfv F (.cv y)))) (.objEq x y)))) (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y))) p0024 p0032
  have p0034 :=
    @g_n_2albidv (syn_wfn F A) (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))) (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y))) x y dv_cache_0009 dv_cache_0010 p0033
  have p0035 :=
    @g_breq1 (.cv x) (.cv y) (.cv z) F
  have p0036_e00_recanon : Nominal.NPrf (.imp (.objEq x y) (syn_wb (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0035
  have p0036 :=
    @g_mo4 (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z)) x y dv_cache_0011 dv_cache_0012 dv_cache_0013 p0036_e00_recanon
  have p0037 :=
    @g_albii (syn_wmo x (syn_wbr (.cv x) F (.cv z))) (.all x (.all y (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y)))) z p0036
  have p0038 :=
    @g_alcom (.all y (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))) z x
  have p0039 :=
    @g_alcom (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y)) z y
  have p0040 :=
    @g_albii (.all z (.all y (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y)))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y)))) x p0039
  have p0041 :=
    @g_n_3bitri (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z)))) (.all z (.all x (.all y (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))))) (.all x (.all z (.all y (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))))) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))))) p0037 p0038 p0040
  have p0042 :=
    @g_r2al (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)) x y A A dv_cache_0014 dv_cache_0013
  have p0043 :=
    @g_n_3bitr4g (syn_wfn F A) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_wbr (.cv y) F (.cv z))) (.objEq x y))))) (.all x (.all y (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y))))) (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z)))) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))) p0034 p0041 p0042
  have p0044 :=
    @g_syl (syn_wf F A B) (syn_wfn F A) (syn_wb (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z)))) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y))))) p0001 p0043
  have p0045 :=
    @g_pm5_32i (syn_wf F A B) (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z)))) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y)))) p0044
  have p0046 :=
    @g_bitri (syn_wf1 F A B) (syn_wa (syn_wf F A B) (.all z (syn_wmo x (syn_wbr (.cv x) F (.cv z))))) (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.objEq x y))))) p0000 p0045
  exact p0046

noncomputable def g_f1fveq
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1 F A B) (syn_wa (.classMem C A) (.classMem D A))) (syn_wb (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.imp (syn_wf1 F A B) (.imp (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_F, fresh_y_not_C, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.imp (syn_wf1 F A B) (.imp (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq C (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_F, fresh_x_not_C, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fveq2 (.cv x) C F
  have p0001 :=
    @g_eqeq1d (.classEq (.cv x) C) (syn_cfv F (.cv x)) (syn_cfv F C) (syn_cfv F (.cv y)) p0000
  have p0002 :=
    @g_eqeq1 (.cv x) C (.cv y)
  have p0003 :=
    @g_imbi12d (.classEq (.cv x) C) (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)) (.classEq C (.cv y)) p0001 p0002
  have p0004 :=
    @g_imbi2d (.classEq (.cv x) C) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))) (.imp (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq C (.cv y))) (syn_wf1 F A B) p0003
  have p0005 :=
    @g_fveq2 (.cv y) D F
  have p0006 :=
    @g_eqeq2d (.classEq (.cv y) D) (syn_cfv F (.cv y)) (syn_cfv F D) (syn_cfv F C) p0005
  have p0007 :=
    @g_eqeq2 (.cv y) D C
  have p0008 :=
    @g_imbi12d (.classEq (.cv y) D) (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C (.cv y)) (.classEq C D) p0006 p0007
  have p0009 :=
    @g_imbi2d (.classEq (.cv y) D) (.imp (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq C (.cv y))) (.imp (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D)) (syn_wf1 F A B) p0008
  have p0010 :=
    @g_dff13 x y A B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0011_e00_recanon : Nominal.NPrf (syn_wb (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0010
  have p0011 :=
    @g_simprbi (syn_wf1 F A B) (syn_wf F A B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))))) p0011_e00_recanon
  have p0012 :=
    @g_rsp2 (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))) x y A A
  have p0013 :=
    @g_syl (syn_wf1 F A B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))))) (.imp (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))) p0011 p0012
  have p0014 :=
    @g_com12 (syn_wf1 F A B) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))) p0013
  have p0015 :=
    @g_vtocl2ga (.imp (syn_wf1 F A B) (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))) (.imp (syn_wf1 F A B) (.imp (.classEq (syn_cfv F C) (syn_cfv F (.cv y))) (.classEq C (.cv y)))) (.imp (syn_wf1 F A B) (.imp (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D))) x y C D A A dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0001 dv_cache_0002 dv_cache_0001 dv_cache_0002 dv_cache_0009 dv_cache_0010 dv_cache_0005 p0004 p0009 p0014
  have p0016 :=
    @g_impcom (syn_wa (.classMem C A) (.classMem D A)) (syn_wf1 F A B) (.imp (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D)) p0015
  have p0017 :=
    @g_fveq2 C D F
  have p0018 :=
    @g_impbid1 (syn_wa (syn_wf1 F A B) (syn_wa (.classMem C A) (.classMem D A))) (.classEq (syn_cfv F C) (syn_cfv F D)) (.classEq C D) p0016 p0017
  exact p0018

noncomputable def g_f1elima
    (A : Class) (B : Class) (F : Class) (X : Class) (Y : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wf1 F A B) (.classMem X A) (syn_wss Y A)) (syn_wb (.classMem (syn_cfv F X) (syn_cima F Y)) (.classMem X Y))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ X.fv ∪ Y.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_Y : z ∉ Y.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (Y).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_Y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cfv F X)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_X, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Wff.classMem X Y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_X, fresh_z_not_Y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_wa (syn_wa (syn_wf1 F A B) (.classMem X A)) (syn_wss Y A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_F, fresh_z_not_X, fresh_z_not_Y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Wff.classEq (syn_cfv F X) (syn_cfv F X))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_X, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_f1fn A B F
  have p0001 :=
    @g_fvelimab z A Y (syn_cfv F X) F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_sylan (syn_wf1 F A B) (syn_wfn F A) (syn_wss Y A) (syn_wb (.classMem (syn_cfv F X) (syn_cima F Y)) (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)))) p0000 p0001
  have p0003 :=
    @g_n_3adant2 (syn_wf1 F A B) (syn_wss Y A) (syn_wb (.classMem (syn_cfv F X) (syn_cima F Y)) (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)))) (.classMem X A) p0002
  have p0004 :=
    @g_ssel Y A (.cv z)
  have p0005 :=
    @g_impac (syn_wss Y A) (.classMem (.cv z) Y) (.classMem (.cv z) A) p0004
  have p0006 :=
    @g_f1fveq A B (.cv z) X F
  have p0007 :=
    @g_ancom2s (syn_wf1 F A B) (.classMem (.cv z) A) (.classMem X A) (syn_wb (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classEq (.cv z) X)) p0006
  have p0008 :=
    @g_biimpd (syn_wa (syn_wf1 F A B) (syn_wa (.classMem X A) (.classMem (.cv z) A))) (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classEq (.cv z) X) p0007
  have p0009 :=
    @g_anassrs (syn_wf1 F A B) (.classMem X A) (.classMem (.cv z) A) (.imp (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classEq (.cv z) X)) p0008
  have p0010 :=
    @g_eleq1 (.cv z) X Y
  have p0011 :=
    @g_biimpcd (.classEq (.cv z) X) (.classMem (.cv z) Y) (.classMem X Y) p0010
  have p0012 :=
    @g_sylan9 (syn_wa (syn_wa (syn_wf1 F A B) (.classMem X A)) (.classMem (.cv z) A)) (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classEq (.cv z) X) (.classMem (.cv z) Y) (.classMem X Y) p0009 p0011
  have p0013 :=
    @g_anasss (syn_wa (syn_wf1 F A B) (.classMem X A)) (.classMem (.cv z) A) (.classMem (.cv z) Y) (.imp (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classMem X Y)) p0012
  have p0014 :=
    @g_sylan2 (syn_wa (syn_wss Y A) (.classMem (.cv z) Y)) (syn_wa (syn_wf1 F A B) (.classMem X A)) (syn_wa (.classMem (.cv z) A) (.classMem (.cv z) Y)) (.imp (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classMem X Y)) p0005 p0013
  have p0015 :=
    @g_anassrs (syn_wa (syn_wf1 F A B) (.classMem X A)) (syn_wss Y A) (.classMem (.cv z) Y) (.imp (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classMem X Y)) p0014
  have p0016 :=
    @g_rexlimdva (syn_wa (syn_wa (syn_wf1 F A B) (.classMem X A)) (syn_wss Y A)) (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classMem X Y) z Y dv_cache_0004 dv_cache_0005 p0015
  have p0017 :=
    @g_n_3impa (syn_wf1 F A B) (.classMem X A) (syn_wss Y A) (.imp (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))) (.classMem X Y)) p0016
  have p0018 :=
    @g_eqid (syn_cfv F X)
  have p0019 :=
    @g_fveq2 (.cv z) X F
  have p0020 :=
    @g_eqeq1d (.classEq (.cv z) X) (syn_cfv F (.cv z)) (syn_cfv F X) (syn_cfv F X) p0019
  have p0021 :=
    @g_rspcev (.classEq (syn_cfv F (.cv z)) (syn_cfv F X)) (.classEq (syn_cfv F X) (syn_cfv F X)) z X Y dv_cache_0006 dv_cache_0001 dv_cache_0007 p0020
  have p0022 :=
    @g_mpan2 (.classMem X Y) (.classEq (syn_cfv F X) (syn_cfv F X)) (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))) p0018 p0021
  have p0023 :=
    @g_impbid1 (syn_w3a (syn_wf1 F A B) (.classMem X A) (syn_wss Y A)) (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))) (.classMem X Y) p0017 p0022
  have p0024 :=
    @g_bitrd (syn_w3a (syn_wf1 F A B) (.classMem X A) (syn_wss Y A)) (.classMem (syn_cfv F X) (syn_cima F Y)) (syn_wrex z Y (.classEq (syn_cfv F (.cv z)) (syn_cfv F X))) (.classMem X Y) p0003 p0023
  exact p0024

noncomputable def g_dff1o6
    (x : Var) (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wf1o F A B) (syn_w3a (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o F A B)))
  have p0001 :=
    @g_dff13 x y A B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002 :=
    (by simpa [syn_wb, syn_wfo] using (Nominal.biimpRefl (syn_wfo F A B)))
  have p0003_e00_recanon : Nominal.NPrf (syn_wb (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0001
  have p0003 :=
    @g_anbi12i (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))))) (syn_wfo F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) p0003_e00_recanon p0002
  have p0004 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))))))))
  have p0005 :=
    @g_eqimss (syn_crn F) B
  have p0006 :=
    @g_anim2i (.classEq (syn_crn F) B) (syn_wss (syn_crn F) B) (syn_wfn F A) p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0008 :=
    @g_sylibr (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) (syn_wf F A B) p0006 p0007
  have p0009 :=
    @g_pm4_71ri (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wf F A B) p0008
  have p0010 :=
    @g_anbi1i (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wa (syn_wf F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y))))) p0009
  have p0011 :=
    @g_an32 (syn_wf F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))))
  have p0012 :=
    @g_n_3bitrri (syn_w3a (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))))) (syn_wa (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))))) (syn_wa (syn_wa (syn_wf F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))))) (syn_wa (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))))) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))) p0004 p0010 p0011
  have p0013 :=
    @g_n_3bitri (syn_wf1o F A B) (syn_wa (syn_wf1 F A B) (syn_wfo F A B)) (syn_wa (syn_wa (syn_wf F A B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))))) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))) (syn_w3a (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wral x A (syn_wral y A (.imp (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv y))) (.classEq (.cv x) (.cv y)))))) p0000 p0003 p0012
  exact p0013

noncomputable def g_f1ocnvfv1
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1o F A B) (.classMem C A)) (.classEq (syn_cfv (syn_ccnv F) (syn_cfv F C)) C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_f1ococnv1 A B F
  have p0001 :=
    @g_fveq1d (syn_wf1o F A B) C (syn_ccom (syn_ccnv F) F) (syn_cres (syn_cid) A) p0000
  have p0002 :=
    @g_adantr (syn_wf1o F A B) (.classEq (syn_cfv (syn_ccom (syn_ccnv F) F) C) (syn_cfv (syn_cres (syn_cid) A) C)) (.classMem C A) p0001
  have p0003 :=
    @g_f1of A B F
  have p0004 :=
    @g_fvco3 A B C (syn_ccnv F) F
  have p0005 :=
    @g_sylan (syn_wf1o F A B) (syn_wf F A B) (.classMem C A) (.classEq (syn_cfv (syn_ccom (syn_ccnv F) F) C) (syn_cfv (syn_ccnv F) (syn_cfv F C))) p0003 p0004
  have p0006 :=
    @g_fvresi A C
  have p0007 :=
    @g_adantl (.classMem C A) (.classEq (syn_cfv (syn_cres (syn_cid) A) C) C) (syn_wf1o F A B) p0006
  have p0008 :=
    @g_n_3eqtr3d (syn_wa (syn_wf1o F A B) (.classMem C A)) (syn_cfv (syn_ccom (syn_ccnv F) F) C) (syn_cfv (syn_cres (syn_cid) A) C) (syn_cfv (syn_ccnv F) (syn_cfv F C)) C p0002 p0005 p0007
  exact p0008

noncomputable def g_f1ocnvfv2
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1o F A B) (.classMem C B)) (.classEq (syn_cfv F (syn_cfv (syn_ccnv F) C)) C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_cnvcnv F
  have p0001 :=
    @g_fveq1i (syn_cfv (syn_ccnv F) C) (syn_ccnv (syn_ccnv F)) F p0000
  have p0002 :=
    @g_f1ocnv A B F
  have p0003 :=
    @g_f1ocnvfv1 B A C (syn_ccnv F)
  have p0004 :=
    @g_sylan (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A) (.classMem C B) (.classEq (syn_cfv (syn_ccnv (syn_ccnv F)) (syn_cfv (syn_ccnv F) C)) C) p0002 p0003
  have p0005 :=
    @g_syl5eqr (syn_wa (syn_wf1o F A B) (.classMem C B)) (syn_cfv F (syn_cfv (syn_ccnv F) C)) (syn_cfv (syn_ccnv (syn_ccnv F)) (syn_cfv (syn_ccnv F) C)) C p0001 p0004
  exact p0005

noncomputable def g_f1ocnvfv
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1o F A B) (.classMem C A)) (.imp (.classEq (syn_cfv F C) D) (.classEq (syn_cfv (syn_ccnv F) D) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  have p0000 :=
    @g_fveq2 D (syn_cfv F C) (syn_ccnv F)
  have p0001 :=
    @g_eqcoms (.classEq (syn_cfv (syn_ccnv F) D) (syn_cfv (syn_ccnv F) (syn_cfv F C))) D (syn_cfv F C) p0000
  have p0002 :=
    @g_f1ocnvfv1 A B C F
  have p0003 :=
    @g_eqeq2d (syn_wa (syn_wf1o F A B) (.classMem C A)) (syn_cfv (syn_ccnv F) (syn_cfv F C)) C (syn_cfv (syn_ccnv F) D) p0002
  have p0004 :=
    @g_syl5ib (.classEq (syn_cfv F C) D) (.classEq (syn_cfv (syn_ccnv F) D) (syn_cfv (syn_ccnv F) (syn_cfv F C))) (syn_wa (syn_wf1o F A B) (.classMem C A)) (.classEq (syn_cfv (syn_ccnv F) D) C) p0001 p0003
  exact p0004

noncomputable def g_f1ocnvfvb
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wf1o F A B) (.classMem C A) (.classMem D B)) (syn_wb (.classEq (syn_cfv F C) D) (.classEq (syn_cfv (syn_ccnv F) D) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  have p0000 :=
    @g_f1ocnvfv A B C D F
  have p0001 :=
    @g_n_3adant3 (syn_wf1o F A B) (.classMem C A) (.imp (.classEq (syn_cfv F C) D) (.classEq (syn_cfv (syn_ccnv F) D) C)) (.classMem D B) p0000
  have p0002 :=
    @g_fveq2 C (syn_cfv (syn_ccnv F) D) F
  have p0003 :=
    @g_eqcoms (.classEq (syn_cfv F C) (syn_cfv F (syn_cfv (syn_ccnv F) D))) C (syn_cfv (syn_ccnv F) D) p0002
  have p0004 :=
    @g_f1ocnvfv2 A B D F
  have p0005 :=
    @g_eqeq2d (syn_wa (syn_wf1o F A B) (.classMem D B)) (syn_cfv F (syn_cfv (syn_ccnv F) D)) D (syn_cfv F C) p0004
  have p0006 :=
    @g_syl5ib (.classEq (syn_cfv (syn_ccnv F) D) C) (.classEq (syn_cfv F C) (syn_cfv F (syn_cfv (syn_ccnv F) D))) (syn_wa (syn_wf1o F A B) (.classMem D B)) (.classEq (syn_cfv F C) D) p0003 p0005
  have p0007 :=
    @g_n_3adant2 (syn_wf1o F A B) (.classMem D B) (.imp (.classEq (syn_cfv (syn_ccnv F) D) C) (.classEq (syn_cfv F C) D)) (.classMem C A) p0006
  have p0008 :=
    @g_impbid (syn_w3a (syn_wf1o F A B) (.classMem C A) (.classMem D B)) (.classEq (syn_cfv F C) D) (.classEq (syn_cfv (syn_ccnv F) D) C) p0001 p0007
  exact p0008

noncomputable def g_f1ocnvdm
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf1o F A B) (.classMem C B)) (.classMem (syn_cfv (syn_ccnv F) C) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_f1ocnv A B F
  have p0001 :=
    @g_f1of B A (syn_ccnv F)
  have p0002 :=
    @g_syl (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A) (syn_wf (syn_ccnv F) B A) p0000 p0001
  have p0003 :=
    @g_ffvelrn B A C (syn_ccnv F)
  have p0004 :=
    @g_sylan (syn_wf1o F A B) (syn_wf (syn_ccnv F) B A) (.classMem C B) (.classMem (syn_cfv (syn_ccnv F) C) A) p0002 p0003
  exact p0004

#print axioms g_f1ocnvdm

end NFChoice.DirectNominalPrf.WPPReplay
