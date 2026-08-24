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
import NominalWPPReplayChunk012ACompact002Part003

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

noncomputable def g_fvun1
    (A : Class) (B : Class) (F : Class) (G : Class) (X : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A))) (.classEq (syn_cfv (syn_cun F G) X) (syn_cfv F X))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.neg (.classMem X B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fnfun A F
  have p0001 :=
    @g_n_3ad2ant1 (syn_wfn F A) (syn_wfn G B) (syn_wfun F) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)) p0000
  have p0002 :=
    @g_fnfun B G
  have p0003 :=
    @g_n_3ad2ant2 (syn_wfn G B) (syn_wfn F A) (syn_wfun G) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)) p0002
  have p0004 :=
    @g_fndm A F
  have p0005 :=
    @g_fndm B G
  have p0006 :=
    @g_ineq12 (syn_cdm F) A (syn_cdm G) B
  have p0007 :=
    @g_syl2an (syn_wfn F A) (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_cin A B)) (syn_wfn G B) p0004 p0005 p0006
  have p0008 :=
    @g_eqeq1d (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_cin (syn_cdm F) (syn_cdm G)) (syn_cin A B) (syn_c0) p0007
  have p0009 :=
    @g_biimprd (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.classEq (syn_cin A B) (syn_c0)) p0008
  have p0010 :=
    @g_adantrd (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.classMem X A) p0009
  have p0011 :=
    @g_n_3impia (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) p0010
  have p0012 :=
    @g_fvun X F G
  have p0013 :=
    @g_syl21anc (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A))) (syn_wfun F) (syn_wfun G) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.classEq (syn_cfv (syn_cun F G) X) (syn_cun (syn_cfv F X) (syn_cfv G X))) p0001 p0003 p0011 p0012
  have p0014 :=
    @g_disj x A B dv_cache_0001 dv_cache_0002
  have p0015 :=
    @g_eleq1 (.cv x) X B
  have p0016 :=
    @g_notbid (.classEq (.cv x) X) (.classMem (.cv x) B) (.classMem X B) p0015
  have p0017 :=
    @g_rspccv (.neg (.classMem (.cv x) B)) (.neg (.classMem X B)) x X A dv_cache_0003 dv_cache_0001 dv_cache_0004 p0016
  have p0018 :=
    @g_sylbi (.classEq (syn_cin A B) (syn_c0)) (syn_wral x A (.neg (.classMem (.cv x) B))) (.imp (.classMem X A) (.neg (.classMem X B))) p0014 p0017
  have p0019 :=
    @g_imp (.classEq (syn_cin A B) (syn_c0)) (.classMem X A) (.neg (.classMem X B)) p0018
  have p0020 :=
    @g_n_3ad2ant3 (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)) (syn_wfn F A) (.neg (.classMem X B)) (syn_wfn G B) p0019
  have p0021 :=
    @g_n_3ad2ant2 (syn_wfn G B) (syn_wfn F A) (.classEq (syn_cdm G) B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)) p0005
  have p0022 :=
    @g_eleq2d (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A))) (syn_cdm G) B X p0021
  have p0023 :=
    @g_mtbird (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A))) (.classMem X (syn_cdm G)) (.classMem X B) p0020 p0022
  have p0024 :=
    @g_ndmfv X G
  have p0025 :=
    @g_syl (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A))) (.neg (.classMem X (syn_cdm G))) (.classEq (syn_cfv G X) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_uneq2d (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A))) (syn_cfv G X) (syn_c0) (syn_cfv F X) p0025
  have p0027 :=
    @g_eqtrd (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A))) (syn_cfv (syn_cun F G) X) (syn_cun (syn_cfv F X) (syn_cfv G X)) (syn_cun (syn_cfv F X) (syn_c0)) p0013 p0026
  have p0028 :=
    @g_un0 (syn_cfv F X)
  have p0029 :=
    @g_syl6eq (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A))) (syn_cfv (syn_cun F G) X) (syn_cun (syn_cfv F X) (syn_c0)) (syn_cfv F X) p0027 p0028
  exact p0029

noncomputable def g_fvun2
    (A : Class) (B : Class) (F : Class) (G : Class) (X : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X B))) (.classEq (syn_cfv (syn_cun F G) X) (syn_cfv G X))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv ∪ X.fv
  have p0000 :=
    @g_uncom F G
  have p0001 :=
    @g_fveq1i X (syn_cun F G) (syn_cun G F) p0000
  have p0002 :=
    @g_incom A B
  have p0003 :=
    @g_eqeq1i (syn_cin A B) (syn_cin B A) (syn_c0) p0002
  have p0004 :=
    @g_anbi1i (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cin B A) (syn_c0)) (.classMem X B) p0003
  have p0005 :=
    @g_fvun1 B A G F X
  have p0006 :=
    @g_syl3an3b (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X B)) (syn_wfn G B) (syn_wfn F A) (syn_wa (.classEq (syn_cin B A) (syn_c0)) (.classMem X B)) (.classEq (syn_cfv (syn_cun G F) X) (syn_cfv G X)) p0004 p0005
  have p0007 :=
    @g_n_3com12 (syn_wfn G B) (syn_wfn F A) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X B)) (.classEq (syn_cfv (syn_cun G F) X) (syn_cfv G X)) p0006
  have p0008 :=
    @g_syl5eq (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X B))) (syn_cfv (syn_cun F G) X) (syn_cfv (syn_cun G F) X) (syn_cfv G X) p0001 p0007
  exact p0008

noncomputable def g_dmfco
    (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun G) (.classMem A (syn_cdm G))) (syn_wb (.classMem A (syn_cdm (syn_ccom F G))) (.classMem (syn_cfv G A) (syn_cdm F)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((syn_cfv G A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wbr (syn_cfv G A) F (.cv z))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_G, fresh_y_ne_z, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_G, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_ccom F G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((syn_cfv G A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fvex A G
  have p0001 :=
    @g_breq1 (.cv y) (syn_cfv G A) (.cv z) F
  have p0002 :=
    @g_ceqsexv (syn_wbr (.cv y) F (.cv z)) (syn_wbr (syn_cfv G A) F (.cv z)) y (syn_cfv G A) dv_cache_0001 dv_cache_0002 p0000 p0001
  have p0003 :=
    @g_eqcom (.cv y) (syn_cfv G A)
  have p0004 :=
    @g_funbrfvb A (.cv y) G
  have p0005 :=
    @g_syl5bb (.classEq (.cv y) (syn_cfv G A)) (.classEq (syn_cfv G A) (.cv y)) (syn_wa (syn_wfun G) (.classMem A (syn_cdm G))) (syn_wbr A G (.cv y)) p0003 p0004
  have p0006 :=
    @g_anbi1d (syn_wa (syn_wfun G) (.classMem A (syn_cdm G))) (.classEq (.cv y) (syn_cfv G A)) (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z)) p0005
  have p0007 :=
    @g_exbidv (syn_wa (syn_wfun G) (.classMem A (syn_cdm G))) (syn_wa (.classEq (.cv y) (syn_cfv G A)) (syn_wbr (.cv y) F (.cv z))) (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z))) y dv_cache_0003 p0006
  have p0008 :=
    @g_syl5rbbr (syn_wbr (syn_cfv G A) F (.cv z)) (syn_wex y (syn_wa (.classEq (.cv y) (syn_cfv G A)) (syn_wbr (.cv y) F (.cv z)))) (syn_wa (syn_wfun G) (.classMem A (syn_cdm G))) (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z)))) p0002 p0007
  have p0009 :=
    @g_exbidv (syn_wa (syn_wfun G) (.classMem A (syn_cdm G))) (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z)))) (syn_wbr (syn_cfv G A) F (.cv z)) z dv_cache_0004 p0008
  have p0010 :=
    @g_eldm z A (syn_ccom F G) dv_cache_0005 dv_cache_0006
  have p0011 :=
    @g_brco y A (.cv z) F G dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0012 :=
    @g_exbii (syn_wbr A (syn_ccom F G) (.cv z)) (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z)))) z p0011
  have p0013 :=
    @g_bitri (.classMem A (syn_cdm (syn_ccom F G))) (syn_wex z (syn_wbr A (syn_ccom F G) (.cv z))) (syn_wex z (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z))))) p0010 p0012
  have p0014 :=
    @g_eldm z (syn_cfv G A) F dv_cache_0011 dv_cache_0012
  have p0015 :=
    @g_n_3bitr4g (syn_wa (syn_wfun G) (.classMem A (syn_cdm G))) (syn_wex z (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z))))) (syn_wex z (syn_wbr (syn_cfv G A) F (.cv z))) (.classMem A (syn_cdm (syn_ccom F G))) (.classMem (syn_cfv G A) (syn_cdm F)) p0009 p0013 p0014
  exact p0015

noncomputable def g_fvco2
    (A : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn G A) (.classMem C A)) (.classEq (syn_cfv (syn_ccom F G) C) (syn_cfv F (syn_cfv G C)))) := by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ F.fv ∪ G.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((syn_wa (syn_wfn G A) (.classMem C A))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, fresh_y_not_A, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wbr C (syn_ccom F G) (.cv z))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, fresh_y_ne_z, fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0004 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_ccom F G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wbr (syn_cfv G C) F (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, fresh_y_not_G, fresh_y_ne_z, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cfv G C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fnsnfv A C G
  have p0001 :=
    @g_imaeq2d (syn_wa (syn_wfn G A) (.classMem C A)) (syn_csn (syn_cfv G C)) (syn_cima G (syn_csn C)) F p0000
  have p0002 :=
    @g_imaco F G (syn_csn C)
  have p0003 :=
    @g_syl6reqr (syn_wa (syn_wfn G A) (.classMem C A)) (syn_cima F (syn_csn (syn_cfv G C))) (syn_cima F (syn_cima G (syn_csn C))) (syn_cima (syn_ccom F G) (syn_csn C)) p0001 p0002
  have p0004 :=
    @g_eqeq1d (syn_wa (syn_wfn G A) (.classMem C A)) (syn_cima (syn_ccom F G) (syn_csn C)) (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y)) p0003
  have p0005 :=
    @g_abbidv (syn_wa (syn_wfn G A) (.classMem C A)) (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y))) (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y))) y dv_cache_0001 p0004
  have p0006 :=
    @g_unieqd (syn_wa (syn_wfn G A) (.classMem C A)) (.cab y (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y)))) (.cab y (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y)))) p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota (syn_wbr C (syn_ccom F G) (.cv z)) z y dv_cache_0002 dv_cache_0003
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv z C (syn_ccom F G) dv_cache_0004 dv_cache_0005
  have p0009 :=
    @g_imasn z C (syn_ccom F G) dv_cache_0004 dv_cache_0005
  have p0010 :=
    @g_eqeq1i (syn_cima (syn_ccom F G) (syn_csn C)) (.cab z (syn_wbr C (syn_ccom F G) (.cv z))) (syn_csn (.cv y)) p0009
  have p0011 :=
    @g_abbii (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y))) (.classEq (.cab z (syn_wbr C (syn_ccom F G) (.cv z))) (syn_csn (.cv y))) y p0010
  have p0012 :=
    @g_unieqi (.cab y (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y)))) (.cab y (.classEq (.cab z (syn_wbr C (syn_ccom F G) (.cv z))) (syn_csn (.cv y)))) p0011
  have p0013 :=
    @g_n_3eqtr4i (syn_cio z (syn_wbr C (syn_ccom F G) (.cv z))) (syn_cuni (.cab y (.classEq (.cab z (syn_wbr C (syn_ccom F G) (.cv z))) (syn_csn (.cv y))))) (syn_cfv (syn_ccom F G) C) (syn_cuni (.cab y (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y))))) p0007 p0008 p0012
  have p0014 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota (syn_wbr (syn_cfv G C) F (.cv z)) z y dv_cache_0006 dv_cache_0003
  have p0015 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv z (syn_cfv G C) F dv_cache_0007 dv_cache_0008
  have p0016 :=
    @g_imasn z (syn_cfv G C) F dv_cache_0007 dv_cache_0008
  have p0017 :=
    @g_eqeq1i (syn_cima F (syn_csn (syn_cfv G C))) (.cab z (syn_wbr (syn_cfv G C) F (.cv z))) (syn_csn (.cv y)) p0016
  have p0018 :=
    @g_abbii (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y))) (.classEq (.cab z (syn_wbr (syn_cfv G C) F (.cv z))) (syn_csn (.cv y))) y p0017
  have p0019 :=
    @g_unieqi (.cab y (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y)))) (.cab y (.classEq (.cab z (syn_wbr (syn_cfv G C) F (.cv z))) (syn_csn (.cv y)))) p0018
  have p0020 :=
    @g_n_3eqtr4i (syn_cio z (syn_wbr (syn_cfv G C) F (.cv z))) (syn_cuni (.cab y (.classEq (.cab z (syn_wbr (syn_cfv G C) F (.cv z))) (syn_csn (.cv y))))) (syn_cfv F (syn_cfv G C)) (syn_cuni (.cab y (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y))))) p0014 p0015 p0019
  have p0021 :=
    @g_n_3eqtr4g (syn_wa (syn_wfn G A) (.classMem C A)) (syn_cuni (.cab y (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y))))) (syn_cuni (.cab y (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y))))) (syn_cfv (syn_ccom F G) C) (syn_cfv F (syn_cfv G C)) p0006 p0013 p0020
  exact p0021

noncomputable def g_fvco
    (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun G) (.classMem A (syn_cdm G))) (.classEq (syn_cfv (syn_ccom F G) A) (syn_cfv F (syn_cfv G A)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_funfn G
  have p0001 :=
    @g_fvco2 (syn_cdm G) A F G
  have p0002 :=
    @g_sylanb (syn_wfun G) (syn_wfn G (syn_cdm G)) (.classMem A (syn_cdm G)) (.classEq (syn_cfv (syn_ccom F G) A) (syn_cfv F (syn_cfv G A))) p0000 p0001
  exact p0002

noncomputable def g_fvco3
    (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wf G A B) (.classMem C A)) (.classEq (syn_cfv (syn_ccom F G) C) (syn_cfv F (syn_cfv G C)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_ffn A B G
  have p0001 :=
    @g_fvco2 A C F G
  have p0002 :=
    @g_sylan (syn_wf G A B) (syn_wfn G A) (.classMem C A) (.classEq (syn_cfv (syn_ccom F G) C) (syn_cfv F (syn_cfv G C))) p0000 p0001
  exact p0002

noncomputable def g_fvopab3ig
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y) (hyp_fvopab3ig_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (hyp_fvopab3ig_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch))) (hyp_fvopab3ig_3 : Nominal.NPrf (.imp (.classMem (.cv x) C) (syn_wmo y ph))) (hyp_fvopab3ig_4 : Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.classMem B D)) (.imp ch (.classEq (syn_cfv F A) B))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0002 : y ∉ ((Wff.classMem (.cv x) C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wa (.classMem A C) ch)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_C_x, dv_ch_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wa (.classMem A C) ch)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_C_y, dv_ch_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_funopab (syn_wa (.classMem (.cv x) C) ph) x y dv_cache_0001
  have p0001 :=
    @g_moanimv (.classMem (.cv x) C) ph y dv_cache_0002
  have p0002 :=
    @g_mpbir (syn_wmo y (syn_wa (.classMem (.cv x) C) ph)) (.imp (.classMem (.cv x) C) (syn_wmo y ph)) hyp_fvopab3ig_3 p0001
  have p0003 :=
    @g_mpgbir (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) C) ph))) (syn_wmo y (syn_wa (.classMem (.cv x) C) ph)) x p0000 p0002
  have p0004 :=
    @g_simpl (.classMem A C) (.classMem B D)
  have p0005 :=
    @g_eleq1 (.cv x) A C
  have p0006 :=
    @g_anbi12d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C) ph ps p0005 hyp_fvopab3ig_1
  have p0007 :=
    @g_anbi2d (.classEq (.cv y) B) ps ch (.classMem A C) hyp_fvopab3ig_2
  have p0008 :=
    @g_opelopabg (syn_wa (.classMem (.cv x) C) ph) (syn_wa (.classMem A C) ps) (syn_wa (.classMem A C) ch) x y A B C D dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0001 p0006 p0007
  have p0009 :=
    @g_biimprd (syn_wa (.classMem A C) (.classMem B D)) (.classMem (syn_cop A B) (syn_copab x y (syn_wa (.classMem (.cv x) C) ph))) (syn_wa (.classMem A C) ch) p0008
  have p0010 :=
    @g_mpand (syn_wa (.classMem A C) (.classMem B D)) (.classMem A C) ch (.classMem (syn_cop A B) (syn_copab x y (syn_wa (.classMem (.cv x) C) ph))) p0004 p0009
  have p0011 :=
    @g_funopfv A B (syn_copab x y (syn_wa (.classMem (.cv x) C) ph))
  have p0012 :=
    @g_ee02 (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) C) ph))) (syn_wa (.classMem A C) (.classMem B D)) ch (.classMem (syn_cop A B) (syn_copab x y (syn_wa (.classMem (.cv x) C) ph))) (.classEq (syn_cfv (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)) A) B) p0003 p0010 p0011
  have p0013 :=
    @g_fveq1i A F (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)) hyp_fvopab3ig_4
  have p0014 :=
    @g_eqeq1i (syn_cfv F A) (syn_cfv (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)) A) B p0013
  have p0015 :=
    @g_syl6ibr (syn_wa (.classMem A C) (.classMem B D)) ch (.classEq (syn_cfv (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)) A) B) (.classEq (syn_cfv F A) B) p0012 p0014
  exact p0015

noncomputable def g_fvopab4g
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y) (hyp_fvopab4g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C))) (hyp_fvopab4g_2 : Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) D) (.classEq (.cv y) B))))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A D) (.classMem C R)) (.classEq (syn_cfv F A) C)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ F.fv
  have dv_cache_0001 : y ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0007 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classEq C C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq C C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_eqid C
  have p0001 :=
    @g_eqeq2d (.classEq (.cv x) A) B C (.cv y) hyp_fvopab4g_1
  have p0002 :=
    @g_eqeq1 (.cv y) C C
  have p0003 :=
    @g_moeq y B dv_cache_0001
  have p0004 :=
    @g_a1i (syn_wmo y (.classEq (.cv y) B)) (.classMem (.cv x) D) p0003
  have p0005 :=
    @g_fvopab3ig (.classEq (.cv y) B) (.classEq (.cv y) C) (.classEq C C) x y A C D R F dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0001 p0002 p0004 hyp_fvopab4g_2
  have p0006 :=
    @g_mpi (syn_wa (.classMem A D) (.classMem C R)) (.classEq C C) (.classEq (syn_cfv F A) C) p0000 p0005
  exact p0006

noncomputable def g_fvopab4
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y) (hyp_fvopab4g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C))) (hyp_fvopab4g_2 : Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) D) (.classEq (.cv y) B))))) (hyp_fvopab4_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem A D) (.classEq (syn_cfv F A) C)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
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
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0007 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_fvopab4g x y A B C D (syn_cvv) F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 hyp_fvopab4g_1 hyp_fvopab4g_2
  have p0001 :=
    @g_mpan2 (.classMem A D) (.classMem C (syn_cvv)) (.classEq (syn_cfv F A) C) hyp_fvopab4_3 p0000
  exact p0001

noncomputable def g_eqfnfv
    (x : Var) (A : Class) (F : Class) (G : Class) (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wb (.classEq F G) (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ F.fv ∪ G.fv
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
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq F G)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wa (syn_wfn F A) (syn_wfn G A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wfn F A) (syn_wfn G A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, dv_A_x, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0007 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_fveq1 (.cv x) F G
  have p0001 :=
    @g_ralrimivw (.classEq F G) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) x A dv_cache_0001 p0000
  have p0002 :=
    @g_pm2_27 (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))
  have p0003 :=
    @g_adantl (.classMem (.cv x) A) (.imp (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (syn_wa (syn_wfn F A) (syn_wfn G A)) p0002
  have p0004 :=
    @g_eqeq1 (syn_cfv F (.cv x)) (syn_cfv G (.cv x)) (.cv y)
  have p0005 :=
    @g_fnopfvb A (.cv x) (.cv y) F
  have p0006 :=
    @g_adantlr (syn_wfn F A) (.classMem (.cv x) A) (syn_wb (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) F)) (syn_wfn G A) p0005
  have p0007 :=
    @g_fnopfvb A (.cv x) (.cv y) G
  have p0008 :=
    @g_adantll (syn_wfn G A) (.classMem (.cv x) A) (syn_wb (.classEq (syn_cfv G (.cv x)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) G)) (syn_wfn F A) p0007
  have p0009 :=
    @g_bibi12d (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classEq (syn_cfv G (.cv x)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) G) p0006 p0008
  have p0010 :=
    @g_syl5ib (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) (syn_wb (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classEq (syn_cfv G (.cv x)) (.cv y))) (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) p0004 p0009
  have p0011 :=
    @g_syld (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) p0003 p0010
  have p0012 :=
    @g_expcom (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A) (.imp (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))) p0011
  have p0013 :=
    @g_opeldm (.cv x) (.cv y) F
  have p0014 :=
    @g_fndm A F
  have p0015 :=
    @g_eleq2d (syn_wfn F A) (syn_cdm F) A (.cv x) p0014
  have p0016 :=
    @g_syl5ib (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm F)) (syn_wfn F A) (.classMem (.cv x) A) p0013 p0015
  have p0017 :=
    @g_adantr (syn_wfn F A) (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) A)) (syn_wfn G A) p0016
  have p0018 :=
    @g_con3d (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) A) p0017
  have p0019 :=
    @g_impcom (syn_wa (syn_wfn F A) (syn_wfn G A)) (.neg (.classMem (.cv x) A)) (.neg (.classMem (syn_cop (.cv x) (.cv y)) F)) p0018
  have p0020 :=
    @g_opeldm (.cv x) (.cv y) G
  have p0021 :=
    @g_fndm A G
  have p0022 :=
    @g_eleq2d (syn_wfn G A) (syn_cdm G) A (.cv x) p0021
  have p0023 :=
    @g_syl5ib (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (.cv x) (syn_cdm G)) (syn_wfn G A) (.classMem (.cv x) A) p0020 p0022
  have p0024 :=
    @g_adantl (syn_wfn G A) (.imp (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (.cv x) A)) (syn_wfn F A) p0023
  have p0025 :=
    @g_con3d (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (.cv x) A) p0024
  have p0026 :=
    @g_impcom (syn_wa (syn_wfn F A) (syn_wfn G A)) (.neg (.classMem (.cv x) A)) (.neg (.classMem (syn_cop (.cv x) (.cv y)) G)) p0025
  have p0027 :=
    @g_n_2falsed (syn_wa (.neg (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (syn_wfn G A))) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G) p0019 p0026
  have p0028 :=
    @g_ex (.neg (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) p0027
  have p0029 :=
    @g_a1dd (.neg (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) p0028
  have p0030 :=
    @g_pm2_61i (.classMem (.cv x) A) (.imp (syn_wa (syn_wfn F A) (syn_wfn G A)) (.imp (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)))) p0012 p0029
  have p0031 :=
    @g_alrimdv (syn_wa (syn_wfn F A) (syn_wfn G A)) (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) y dv_cache_0002 dv_cache_0003 p0030
  have p0032 :=
    @g_alimdv (syn_wa (syn_wfn F A) (syn_wfn G A)) (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))) x dv_cache_0004 p0031
  have p0033 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))))
  have p0034 :=
    @g_eqrel x y F G dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0035 :=
    @g_n_3imtr4g (syn_wa (syn_wfn F A) (syn_wfn G A)) (.all x (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))) (.all x (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)))) (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (.classEq F G) p0032 p0033 p0034
  have p0036 :=
    @g_impbid2 (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classEq F G) (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) p0001 p0035
  exact p0036

#print axioms g_eqfnfv

end NFChoice.DirectNominalPrf.WPPReplay
