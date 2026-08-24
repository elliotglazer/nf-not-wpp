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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk011Compact001Part011

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

noncomputable def g_funun
    (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (syn_wfun (syn_cun F G))) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_G : z ∉ G.fv := by
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
  have dv_cache_0001 : x ∉ ((syn_cdm F)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cdm G)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0005 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cun F G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_cun F G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cun F G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elun (syn_cop (.cv x) (.cv y)) F G
  have p0001 :=
    @g_elun (syn_cop (.cv x) (.cv z)) F G
  have p0002 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G)) (syn_wo (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G)) (syn_wo (.classMem (syn_cop (.cv x) (.cv z)) F) (.classMem (syn_cop (.cv x) (.cv z)) G)) p0000 p0001
  have p0003 :=
    @g_anddi (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F) (.classMem (syn_cop (.cv x) (.cv z)) G)
  have p0004 :=
    @g_bitri (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))) (syn_wa (syn_wo (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) (syn_wo (.classMem (syn_cop (.cv x) (.cv z)) F) (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wo (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G)))) p0002 p0003
  have p0005 :=
    @g_sp (.imp (.classMem (.cv x) (syn_cdm F)) (.neg (.classMem (.cv x) (syn_cdm G)))) x
  have p0006 :=
    @g_disj1 x (syn_cdm F) (syn_cdm G) dv_cache_0001 dv_cache_0002
  have p0007 :=
    @g_imnan (.classMem (.cv x) (syn_cdm F)) (.classMem (.cv x) (syn_cdm G))
  have p0008 :=
    @g_bicomi (.imp (.classMem (.cv x) (syn_cdm F)) (.neg (.classMem (.cv x) (syn_cdm G)))) (.neg (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (.cv x) (syn_cdm G)))) p0007
  have p0009 :=
    @g_n_3imtr4i (.all x (.imp (.classMem (.cv x) (syn_cdm F)) (.neg (.classMem (.cv x) (syn_cdm G))))) (.imp (.classMem (.cv x) (syn_cdm F)) (.neg (.classMem (.cv x) (syn_cdm G)))) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.neg (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (.cv x) (syn_cdm G)))) p0005 p0006 p0008
  have p0010 :=
    @g_opeldm (.cv x) (.cv y) F
  have p0011 :=
    @g_opeldm (.cv x) (.cv z) G
  have p0012 :=
    @g_anim12i (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_cop (.cv x) (.cv z)) G) (.classMem (.cv x) (syn_cdm G)) p0010 p0011
  have p0013 :=
    @g_nsyl (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (.cv x) (syn_cdm G))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) G)) p0009 p0012
  have p0014 :=
    @g_orel2 (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) G)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F))
  have p0015 :=
    @g_syl (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.neg (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) G))) (.imp (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F))) p0013 p0014
  have p0016 :=
    @g_sp (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F)))) x
  have p0017 :=
    @g_incom (syn_cdm F) (syn_cdm G)
  have p0018 :=
    @g_eqeq1i (syn_cin (syn_cdm F) (syn_cdm G)) (syn_cin (syn_cdm G) (syn_cdm F)) (syn_c0) p0017
  have p0019 :=
    @g_disj1 x (syn_cdm G) (syn_cdm F) dv_cache_0002 dv_cache_0001
  have p0020 :=
    @g_bitri (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.classEq (syn_cin (syn_cdm G) (syn_cdm F)) (syn_c0)) (.all x (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F))))) p0018 p0019
  have p0021 :=
    @g_imnan (.classMem (.cv x) (syn_cdm G)) (.classMem (.cv x) (syn_cdm F))
  have p0022 :=
    @g_bicomi (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F)))) (.neg (syn_wa (.classMem (.cv x) (syn_cdm G)) (.classMem (.cv x) (syn_cdm F)))) p0021
  have p0023 :=
    @g_n_3imtr4i (.all x (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F))))) (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F)))) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.neg (syn_wa (.classMem (.cv x) (syn_cdm G)) (.classMem (.cv x) (syn_cdm F)))) p0016 p0020 p0022
  have p0024 :=
    @g_opeldm (.cv x) (.cv y) G
  have p0025 :=
    @g_opeldm (.cv x) (.cv z) F
  have p0026 :=
    @g_anim12i (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (.cv x) (syn_cdm G)) (.classMem (syn_cop (.cv x) (.cv z)) F) (.classMem (.cv x) (syn_cdm F)) p0024 p0025
  have p0027 :=
    @g_nsyl (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (syn_wa (.classMem (.cv x) (syn_cdm G)) (.classMem (.cv x) (syn_cdm F))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F)) p0023 p0026
  have p0028 :=
    @g_orel1 (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G))
  have p0029 :=
    @g_syl (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.neg (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F))) (.imp (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G))) p0027 p0028
  have p0030 :=
    @g_orim12d (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G)) p0015 p0029
  have p0031 :=
    @g_syl5bi (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))) (syn_wo (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G)))) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G))) p0004 p0030
  have p0032 :=
    @g_dffun4 x y z F dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0033 :=
    @g_biimpi (syn_wfun F) (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (.objEq y z))))) p0032
  have p0034 :=
    @g_n_19_21bi (syn_wfun F) (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (.objEq y z)))) x p0033
  have p0035 :=
    @g_n_19_21bbi (syn_wfun F) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (.objEq y z)) y z p0034
  have p0036 :=
    @g_dffun4 x y z G dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0037 :=
    @g_biimpi (syn_wfun G) (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G)) (.objEq y z))))) p0036
  have p0038 :=
    @g_n_19_21bi (syn_wfun G) (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G)) (.objEq y z)))) x p0037
  have p0039 :=
    @g_n_19_21bbi (syn_wfun G) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G)) (.objEq y z)) y z p0038
  have p0040 :=
    @g_jaao (syn_wfun F) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (.objEq y z) (syn_wfun G) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G)) p0035 p0039
  have p0041 :=
    @g_sylan9r (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))) (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wa (syn_wfun F) (syn_wfun G)) (.objEq y z) p0031 p0040
  have p0042 :=
    @g_alrimiv (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))) (.objEq y z)) z dv_cache_0012 p0041
  have p0043 :=
    @g_alrimivv (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))) (.objEq y z))) x y dv_cache_0013 dv_cache_0014 p0042
  have p0044 :=
    @g_dffun4 x y z (syn_cun F G) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0045 :=
    @g_sylibr (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))) (.objEq y z))))) (syn_wfun (syn_cun F G)) p0043 p0044
  exact p0045

noncomputable def g_funsn
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wfun (syn_csn (syn_cop A B))) := by
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
  have dv_cache_0001 : x ∉ ((syn_csn (syn_cop A B))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_csn (syn_cop A B))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.classEq (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dffun6 x y (syn_csn (syn_cop A B)) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_moeq y B dv_cache_0004
  have p0002 :=
    @g_a1i (syn_wmo y (.classEq (.cv y) B)) (.classEq (.cv x) A) p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))))
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_opex (.cv x) (.cv y) p0004 p0005
  have p0007 :=
    @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop A B) p0006
  have p0008 :=
    @g_opth (.cv x) (.cv y) A B
  have p0009 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B)) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0007 p0008
  have p0010 :=
    @g_bitri (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B))) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0003 p0009
  have p0011 :=
    @g_mobii (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) y p0010
  have p0012 :=
    @g_moanimv (.classEq (.cv x) A) (.classEq (.cv y) B) y dv_cache_0005
  have p0013 :=
    @g_bitri (syn_wmo y (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))) (syn_wmo y (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))) (.imp (.classEq (.cv x) A) (syn_wmo y (.classEq (.cv y) B))) p0011 p0012
  have p0014 :=
    @g_mpbir (syn_wmo y (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))) (.imp (.classEq (.cv x) A) (syn_wmo y (.classEq (.cv y) B))) p0002 p0013
  have p0015 :=
    @g_mpgbir (syn_wfun (syn_csn (syn_cop A B))) (syn_wmo y (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))) x p0000 p0014
  exact p0015

noncomputable def g_fnsn
    (A : Class) (B : Class) (hyp_fnsn_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fnsn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_csn (syn_cop A B)) (syn_csn A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_funsn A B
  have p0001 :=
    @g_dmsnop A B hyp_fnsn_2
  have p0002 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_csn (syn_cop A B)) (syn_csn A))))
  have p0003 :=
    @g_mpbir2an (syn_wfn (syn_csn (syn_cop A B)) (syn_csn A)) (syn_wfun (syn_csn (syn_cop A B))) (.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A)) p0000 p0001 p0002
  exact p0003

noncomputable def g_fun0
     :
    Nominal.NPrf (syn_wfun (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_co01 (syn_ccnv (syn_c0))
  have p0001 :=
    @g_n_0ss (syn_cid)
  have p0002 :=
    @g_eqsstri (syn_ccom (syn_c0) (syn_ccnv (syn_c0))) (syn_c0) (syn_cid) p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wfun] using (Nominal.biimpRefl (syn_wfun (syn_c0))))
  have p0004 :=
    @g_mpbir (syn_wfun (syn_c0)) (syn_wss (syn_ccom (syn_c0) (syn_ccnv (syn_c0))) (syn_cid)) p0002 p0003
  exact p0004

noncomputable def g_funcnv2
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wfun (syn_ccnv A)) (.all y (syn_wmo x (syn_wbr (.cv x) A (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have dv_cache_0001 : y ∉ ((syn_ccnv A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ccnv A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 :=
    @g_dffun6 y x (syn_ccnv A) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_brcnv (.cv y) (.cv x) A
  have p0002 :=
    @g_mobii (syn_wbr (.cv y) (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A (.cv y)) x p0001
  have p0003 :=
    @g_albii (syn_wmo x (syn_wbr (.cv y) (syn_ccnv A) (.cv x))) (syn_wmo x (syn_wbr (.cv x) A (.cv y))) y p0002
  have p0004 :=
    @g_bitri (syn_wfun (syn_ccnv A)) (.all y (syn_wmo x (syn_wbr (.cv y) (syn_ccnv A) (.cv x)))) (.all y (syn_wmo x (syn_wbr (.cv x) A (.cv y)))) p0000 p0003
  exact p0004

#print axioms g_funcnv2

end NFChoice.DirectNominalPrf.WPPReplay
