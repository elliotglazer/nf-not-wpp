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
import NominalWPPReplayChunk011Compact001Part014

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

noncomputable def g_imadif
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun (syn_ccnv F)) (.classEq (syn_cima F (syn_cdif A B)) (syn_cdif (syn_cima F A) (syn_cima F B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
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
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((syn_wfun (syn_ccnv F))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_ccnv F)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cdif A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cima F (syn_cdif A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cdif (syn_cima F A) (syn_cima F B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_wfun (syn_ccnv F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_anandir (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))
  have p0001 :=
    @g_exbii (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y)))) x p0000
  have p0002 :=
    @g_n_19_40 (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))) x
  have p0003 :=
    @g_sylbi (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y)))) (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))))) (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (syn_wex x (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))))) p0001 p0002
  have p0004 :=
    @g_nfv (syn_wfun (syn_ccnv F)) x dv_cache_0001
  have p0005 :=
    @g_nfe1 (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))) x
  have p0006 :=
    @g_nfan (syn_wfun (syn_ccnv F)) (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))) x p0004 p0005
  have p0007 :=
    @g_funmo x (.cv y) (syn_ccnv F) dv_cache_0002 dv_cache_0003
  have p0008 :=
    @g_brcnv (.cv y) (.cv x) F
  have p0009 :=
    @g_mobii (syn_wbr (.cv y) (syn_ccnv F) (.cv x)) (syn_wbr (.cv x) F (.cv y)) x p0008
  have p0010 :=
    @g_sylib (syn_wfun (syn_ccnv F)) (syn_wmo x (syn_wbr (.cv y) (syn_ccnv F) (.cv x))) (syn_wmo x (syn_wbr (.cv x) F (.cv y))) p0007 p0009
  have p0011 :=
    @g_mopick (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)) x
  have p0012 :=
    @g_sylan (syn_wfun (syn_ccnv F)) (syn_wmo x (syn_wbr (.cv x) F (.cv y))) (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))) (.imp (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))) p0010 p0011
  have p0013 :=
    @g_con2d (syn_wa (syn_wfun (syn_ccnv F)) (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))))) (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) B) p0012
  have p0014 :=
    @g_imnan (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))
  have p0015 :=
    @g_sylib (syn_wa (syn_wfun (syn_ccnv F)) (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))))) (.imp (.classMem (.cv x) B) (.neg (syn_wbr (.cv x) F (.cv y)))) (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))) p0013 p0014
  have p0016 :=
    @g_alrimi (syn_wa (syn_wfun (syn_ccnv F)) (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B))))) (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))) x p0006 p0015
  have p0017 :=
    @g_ex (syn_wfun (syn_ccnv F)) (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))) (.all x (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) p0016
  have p0018 :=
    @g_exancom (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)) x
  have p0019 :=
    @g_alnex (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))) x
  have p0020 :=
    @g_n_3imtr3g (syn_wfun (syn_ccnv F)) (syn_wex x (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (.classMem (.cv x) B)))) (.all x (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) (syn_wex x (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y)))) (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) p0017 p0018 p0019
  have p0021 :=
    @g_anim2d (syn_wfun (syn_ccnv F)) (syn_wex x (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y)))) (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) p0020
  have p0022 :=
    @g_syl5 (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y)))) (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (syn_wex x (syn_wa (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))))) (syn_wfun (syn_ccnv F)) (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))) p0003 p0021
  have p0023 :=
    @g_n_19_29r (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))) x
  have p0024 :=
    @g_sylan2br (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (.all x (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))) p0019 p0023
  have p0025 :=
    @g_andi (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (.classMem (.cv x) B)) (.neg (syn_wbr (.cv x) F (.cv y)))
  have p0026 :=
    @g_ianor (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))
  have p0027 :=
    @g_anbi2i (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))) (syn_wo (.neg (.classMem (.cv x) B)) (.neg (syn_wbr (.cv x) F (.cv y)))) (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) p0026
  have p0028 :=
    @g_an32 (.classMem (.cv x) A) (.neg (.classMem (.cv x) B)) (syn_wbr (.cv x) F (.cv y))
  have p0029 :=
    @g_pm3_24 (syn_wbr (.cv x) F (.cv y))
  have p0030 :=
    @g_intnan (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (syn_wbr (.cv x) F (.cv y)))) (.classMem (.cv x) A) p0029
  have p0031 :=
    @g_anass (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)) (.neg (syn_wbr (.cv x) F (.cv y)))
  have p0032 :=
    @g_mtbir (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (syn_wbr (.cv x) F (.cv y)))) (syn_wa (.classMem (.cv x) A) (syn_wa (syn_wbr (.cv x) F (.cv y)) (.neg (syn_wbr (.cv x) F (.cv y))))) p0030 p0031
  have p0033 :=
    @g_biorfi (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (syn_wbr (.cv x) F (.cv y)))) (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (.classMem (.cv x) B))) p0032
  have p0034 :=
    @g_bitri (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (.classMem (.cv x) B))) (syn_wo (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (.classMem (.cv x) B))) (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (syn_wbr (.cv x) F (.cv y))))) p0028 p0033
  have p0035 :=
    @g_n_3bitr4i (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (syn_wo (.neg (.classMem (.cv x) B)) (.neg (syn_wbr (.cv x) F (.cv y))))) (syn_wo (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (.classMem (.cv x) B))) (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (syn_wbr (.cv x) F (.cv y))))) (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y))) p0025 p0027 p0034
  have p0036 :=
    @g_exbii (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y))) x p0035
  have p0037 :=
    @g_sylib (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))) (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) (.neg (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))) (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y)))) p0024 p0036
  have p0038 :=
    @g_impbid1 (syn_wfun (syn_ccnv F)) (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y)))) (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))) p0022 p0037
  have p0039 :=
    @g_elima2 x (.cv y) F (syn_cdif A B) dv_cache_0002 dv_cache_0004 dv_cache_0005
  have p0040 :=
    @g_eldif (.cv x) A B
  have p0041 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdif A B)) (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y)) p0040
  have p0042 :=
    @g_exbii (syn_wa (.classMem (.cv x) (syn_cdif A B)) (syn_wbr (.cv x) F (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y))) x p0041
  have p0043 :=
    @g_bitri (.classMem (.cv y) (syn_cima F (syn_cdif A B))) (syn_wex x (syn_wa (.classMem (.cv x) (syn_cdif A B)) (syn_wbr (.cv x) F (.cv y)))) (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y)))) p0039 p0042
  have p0044 :=
    @g_eldif (.cv y) (syn_cima F A) (syn_cima F B)
  have p0045 :=
    @g_elima2 x (.cv y) F A dv_cache_0002 dv_cache_0004 dv_cache_0006
  have p0046 :=
    @g_elima2 x (.cv y) F B dv_cache_0002 dv_cache_0004 dv_cache_0007
  have p0047 :=
    @g_notbii (.classMem (.cv y) (syn_cima F B)) (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))) p0046
  have p0048 :=
    @g_anbi12i (.classMem (.cv y) (syn_cima F A)) (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (.neg (.classMem (.cv y) (syn_cima F B))) (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y))))) p0045 p0047
  have p0049 :=
    @g_bitri (.classMem (.cv y) (syn_cdif (syn_cima F A) (syn_cima F B))) (syn_wa (.classMem (.cv y) (syn_cima F A)) (.neg (.classMem (.cv y) (syn_cima F B)))) (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))) p0044 p0048
  have p0050 :=
    @g_n_3bitr4g (syn_wfun (syn_ccnv F)) (syn_wex x (syn_wa (syn_wa (.classMem (.cv x) A) (.neg (.classMem (.cv x) B))) (syn_wbr (.cv x) F (.cv y)))) (syn_wa (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (.neg (syn_wex x (syn_wa (.classMem (.cv x) B) (syn_wbr (.cv x) F (.cv y)))))) (.classMem (.cv y) (syn_cima F (syn_cdif A B))) (.classMem (.cv y) (syn_cdif (syn_cima F A) (syn_cima F B))) p0038 p0043 p0049
  have p0051 :=
    @g_eqrdv (syn_wfun (syn_ccnv F)) y (syn_cima F (syn_cdif A B)) (syn_cdif (syn_cima F A) (syn_cima F B)) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0050
  exact p0051

noncomputable def g_imain
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun (syn_ccnv F)) (.classEq (syn_cima F (syn_cin A B)) (syn_cin (syn_cima F A) (syn_cima F B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_imadif A (syn_cdif A B) F
  have p0001 :=
    @g_imadif A B F
  have p0002 :=
    @g_difeq2d (syn_wfun (syn_ccnv F)) (syn_cima F (syn_cdif A B)) (syn_cdif (syn_cima F A) (syn_cima F B)) (syn_cima F A) p0001
  have p0003 :=
    @g_eqtrd (syn_wfun (syn_ccnv F)) (syn_cima F (syn_cdif A (syn_cdif A B))) (syn_cdif (syn_cima F A) (syn_cima F (syn_cdif A B))) (syn_cdif (syn_cima F A) (syn_cdif (syn_cima F A) (syn_cima F B))) p0000 p0002
  have p0004 :=
    @g_dfin4 A B
  have p0005 :=
    @g_imaeq2i (syn_cin A B) (syn_cdif A (syn_cdif A B)) F p0004
  have p0006 :=
    @g_dfin4 (syn_cima F A) (syn_cima F B)
  have p0007 :=
    @g_n_3eqtr4g (syn_wfun (syn_ccnv F)) (syn_cima F (syn_cdif A (syn_cdif A B))) (syn_cdif (syn_cima F A) (syn_cdif (syn_cima F A) (syn_cima F B))) (syn_cima F (syn_cin A B)) (syn_cin (syn_cima F A) (syn_cima F B)) p0003 p0005 p0006
  exact p0007

noncomputable def g_fneq1
    (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wfn F A) (syn_wfn G A))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_funeq F G
  have p0001 :=
    @g_dmeq F G
  have p0002 :=
    @g_eqeq1d (.classEq F G) (syn_cdm F) (syn_cdm G) A p0001
  have p0003 :=
    @g_anbi12d (.classEq F G) (syn_wfun F) (syn_wfun G) (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) A) p0000 p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn F A)))
  have p0005 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn G A)))
  have p0006 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A)) (syn_wa (syn_wfun G) (.classEq (syn_cdm G) A)) (syn_wfn F A) (syn_wfn G A) p0003 p0004 p0005
  exact p0006

noncomputable def g_fneq2
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wfn F A) (syn_wfn F B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_eqeq2 A B (syn_cdm F)
  have p0001 :=
    @g_anbi2d (.classEq A B) (.classEq (syn_cdm F) A) (.classEq (syn_cdm F) B) (syn_wfun F) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn F A)))
  have p0003 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn F B)))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A)) (syn_wa (syn_wfun F) (.classEq (syn_cdm F) B)) (syn_wfn F A) (syn_wfn F B) p0001 p0002 p0003
  exact p0004

noncomputable def g_fneq1d
    (ph : Wff) (A : Class) (F : Class) (G : Class) (hyp_fneq1d_1 : Nominal.NPrf (.imp ph (.classEq F G))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wfn F A) (syn_wfn G A))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fneq1 A F G
  have p0001 :=
    @g_syl ph (.classEq F G) (syn_wb (syn_wfn F A) (syn_wfn G A)) hyp_fneq1d_1 p0000
  exact p0001

noncomputable def g_fneq2d
    (ph : Wff) (A : Class) (B : Class) (F : Class) (hyp_fneq2d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wfn F A) (syn_wfn F B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fneq2 A B F
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wfn F A) (syn_wfn F B)) hyp_fneq2d_1 p0000
  exact p0001

noncomputable def g_fneq1i
    (A : Class) (F : Class) (G : Class) (hyp_fneq1i_1 : Nominal.NPrf (.classEq F G)) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wfn G A)) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fneq1 A F G
  have p0001 :=
    Nominal.mp hyp_fneq1i_1 p0000
  exact p0001

noncomputable def g_fneq2i
    (A : Class) (B : Class) (F : Class) (hyp_fneq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wfn F A) (syn_wfn F B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fneq2 A B F
  have p0001 :=
    Nominal.mp hyp_fneq2i_1 p0000
  exact p0001

noncomputable def g_fnfun
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (syn_wfun F)) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn F A)))
  have p0001 :=
    @g_simplbi (syn_wfn F A) (syn_wfun F) (.classEq (syn_cdm F) A) p0000
  exact p0001

noncomputable def g_fndm
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (.classEq (syn_cdm F) A)) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn F A)))
  have p0001 :=
    @g_simprbi (syn_wfn F A) (syn_wfun F) (.classEq (syn_cdm F) A) p0000
  exact p0001

noncomputable def g_funfni
    (ph : Wff) (A : Class) (B : Class) (F : Class) (hyp_funfni_1 : Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem B (syn_cdm F))) ph)) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem B A)) ph) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fnfun A F
  have p0001 :=
    @g_adantr (syn_wfn F A) (syn_wfun F) (.classMem B A) p0000
  have p0002 :=
    @g_fndm A F
  have p0003 :=
    @g_eleq2d (syn_wfn F A) (syn_cdm F) A B p0002
  have p0004 :=
    @g_biimpar (syn_wfn F A) (.classMem B (syn_cdm F)) (.classMem B A) p0003
  have p0005 :=
    @g_syl2anc (syn_wa (syn_wfn F A) (.classMem B A)) (syn_wfun F) (.classMem B (syn_cdm F)) ph p0001 p0004 hyp_funfni_1
  exact p0005

noncomputable def g_fnbr
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (syn_wbr B F C)) (.classMem B A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_fndm A F
  have p0001 :=
    @g_breldm B C F
  have p0002 :=
    @g_adantl (syn_wbr B F C) (.classMem B (syn_cdm F)) (.classEq (syn_cdm F) A) p0001
  have p0003 :=
    @g_simpl (.classEq (syn_cdm F) A) (syn_wbr B F C)
  have p0004 :=
    @g_eleqtrd (syn_wa (.classEq (syn_cdm F) A) (syn_wbr B F C)) B (syn_cdm F) A p0002 p0003
  have p0005 :=
    @g_sylan (syn_wfn F A) (.classEq (syn_cdm F) A) (syn_wbr B F C) (.classMem B A) p0000 p0004
  exact p0005

noncomputable def g_fnop
    (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem (syn_cop B C) F)) (.classMem B A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr B F C)))
  have p0001 :=
    @g_fnbr A B C F
  have p0002 :=
    @g_sylan2br (.classMem (syn_cop B C) F) (syn_wfn F A) (syn_wbr B F C) (.classMem B A) p0000 p0001
  exact p0002

noncomputable def g_fneu
    (y : Var) (A : Class) (B : Class) (F : Class) (dv_B_y : y ∉ B.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem B A)) (syn_weu y (syn_wbr B F (.cv y)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cdm F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.imp (syn_wfun F) (syn_weu y (syn_wbr B F (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_B, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_breq1 (.cv x) B (.cv y) F
  have p0001 :=
    @g_eubidv (.classEq (.cv x) B) (syn_wbr (.cv x) F (.cv y)) (syn_wbr B F (.cv y)) y dv_cache_0001 p0000
  have p0002 :=
    @g_imbi2d (.classEq (.cv x) B) (syn_weu y (syn_wbr (.cv x) F (.cv y))) (syn_weu y (syn_wbr B F (.cv y))) (syn_wfun F) p0001
  have p0003 :=
    @g_eldm y (.cv x) F dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_funmo y (.cv x) F dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_exmoeu2 (syn_wbr (.cv x) F (.cv y)) y
  have p0006 :=
    @g_syl5ib (syn_wfun F) (syn_wmo y (syn_wbr (.cv x) F (.cv y))) (syn_wex y (syn_wbr (.cv x) F (.cv y))) (syn_weu y (syn_wbr (.cv x) F (.cv y))) p0004 p0005
  have p0007 :=
    @g_sylbi (.classMem (.cv x) (syn_cdm F)) (syn_wex y (syn_wbr (.cv x) F (.cv y))) (.imp (syn_wfun F) (syn_weu y (syn_wbr (.cv x) F (.cv y)))) p0003 p0006
  have p0008 :=
    @g_vtoclga (.imp (syn_wfun F) (syn_weu y (syn_wbr (.cv x) F (.cv y)))) (.imp (syn_wfun F) (syn_weu y (syn_wbr B F (.cv y)))) x B (syn_cdm F) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0002 p0007
  have p0009 :=
    @g_impcom (.classMem B (syn_cdm F)) (syn_wfun F) (syn_weu y (syn_wbr B F (.cv y))) p0008
  have p0010 :=
    @g_funfni (syn_weu y (syn_wbr B F (.cv y))) A B F p0009
  exact p0010

noncomputable def g_fneu2
    (y : Var) (A : Class) (B : Class) (F : Class) (dv_B_y : y ∉ B.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (.classMem B A)) (syn_weu y (.classMem (syn_cop B (.cv y)) F))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : y ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fneu y A B F dv_cache_0001 dv_cache_0002
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr B F (.cv y))))
  have p0002 :=
    @g_eubii (syn_wbr B F (.cv y)) (.classMem (syn_cop B (.cv y)) F) y p0001
  have p0003 :=
    @g_sylib (syn_wa (syn_wfn F A) (.classMem B A)) (syn_weu y (syn_wbr B F (.cv y))) (syn_weu y (.classMem (syn_cop B (.cv y)) F)) p0000 p0002
  exact p0003

noncomputable def g_fnun
    (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfn (syn_cun F G) (syn_cun A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn F A)))
  have p0001 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn G B)))
  have p0002 :=
    @g_ineq12 (syn_cdm F) A (syn_cdm G) B
  have p0003 :=
    @g_eqeq1d (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)) (syn_cin (syn_cdm F) (syn_cdm G)) (syn_cin A B) (syn_c0) p0002
  have p0004 :=
    @g_anbi2d (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.classEq (syn_cin A B) (syn_c0)) (syn_wa (syn_wfun F) (syn_wfun G)) p0003
  have p0005 :=
    @g_funun F G
  have p0006 :=
    @g_syl6bir (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)) (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin A B) (syn_c0))) (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (syn_wfun (syn_cun F G)) p0004 p0005
  have p0007 :=
    @g_dmun F G
  have p0008 :=
    @g_uneq12 (syn_cdm F) A (syn_cdm G) B
  have p0009 :=
    @g_syl5eq (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)) (syn_cdm (syn_cun F G)) (syn_cun (syn_cdm F) (syn_cdm G)) (syn_cun A B) p0007 p0008
  have p0010 :=
    @g_jctird (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)) (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin A B) (syn_c0))) (syn_wfun (syn_cun F G)) (.classEq (syn_cdm (syn_cun F G)) (syn_cun A B)) p0006 p0009
  have p0011 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_cun F G) (syn_cun A B))))
  have p0012 :=
    @g_syl6ibr (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)) (syn_wa (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin A B) (syn_c0))) (syn_wa (syn_wfun (syn_cun F G)) (.classEq (syn_cdm (syn_cun F G)) (syn_cun A B))) (syn_wfn (syn_cun F G) (syn_cun A B)) p0010 p0011
  have p0013 :=
    @g_exp3a (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)) (syn_wa (syn_wfun F) (syn_wfun G)) (.classEq (syn_cin A B) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A B)) p0012
  have p0014 :=
    @g_impcom (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)) (syn_wa (syn_wfun F) (syn_wfun G)) (.imp (.classEq (syn_cin A B) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A B))) p0013
  have p0015 :=
    @g_an4s (syn_wfun F) (syn_wfun G) (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B) (.imp (.classEq (syn_cin A B) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A B))) p0014
  have p0016 :=
    @g_syl2anb (syn_wfn F A) (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A)) (syn_wa (syn_wfun G) (.classEq (syn_cdm G) B)) (.imp (.classEq (syn_cin A B) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A B))) (syn_wfn G B) p0000 p0001 p0015
  have p0017 :=
    @g_imp (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0)) (syn_wfn (syn_cun F G) (syn_cun A B)) p0016
  exact p0017

noncomputable def g_fnco
    (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wss (syn_crn G) A)) (syn_wfn (syn_ccom F G) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fnfun A F
  have p0001 :=
    @g_fnfun B G
  have p0002 :=
    @g_funco F G
  have p0003 :=
    @g_syl2an (syn_wfn F A) (syn_wfun F) (syn_wfun G) (syn_wfun (syn_ccom F G)) (syn_wfn G B) p0000 p0001 p0002
  have p0004 :=
    @g_n_3adant3 (syn_wfn F A) (syn_wfn G B) (syn_wfun (syn_ccom F G)) (syn_wss (syn_crn G) A) p0003
  have p0005 :=
    @g_fndm A F
  have p0006 :=
    @g_sseq2d (syn_wfn F A) (syn_cdm F) A (syn_crn G) p0005
  have p0007 :=
    @g_biimpar (syn_wfn F A) (syn_wss (syn_crn G) (syn_cdm F)) (syn_wss (syn_crn G) A) p0006
  have p0008 :=
    @g_dmcosseq F G
  have p0009 :=
    @g_syl (syn_wa (syn_wfn F A) (syn_wss (syn_crn G) A)) (syn_wss (syn_crn G) (syn_cdm F)) (.classEq (syn_cdm (syn_ccom F G)) (syn_cdm G)) p0007 p0008
  have p0010 :=
    @g_n_3adant2 (syn_wfn F A) (syn_wss (syn_crn G) A) (.classEq (syn_cdm (syn_ccom F G)) (syn_cdm G)) (syn_wfn G B) p0009
  have p0011 :=
    @g_fndm B G
  have p0012 :=
    @g_n_3ad2ant2 (syn_wfn G B) (syn_wfn F A) (.classEq (syn_cdm G) B) (syn_wss (syn_crn G) A) p0011
  have p0013 :=
    @g_eqtrd (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wss (syn_crn G) A)) (syn_cdm (syn_ccom F G)) (syn_cdm G) B p0010 p0012
  have p0014 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_ccom F G) B)))
  have p0015 :=
    @g_sylanbrc (syn_w3a (syn_wfn F A) (syn_wfn G B) (syn_wss (syn_crn G) A)) (syn_wfun (syn_ccom F G)) (.classEq (syn_cdm (syn_ccom F G)) B) (syn_wfn (syn_ccom F G) B) p0004 p0013 p0014
  exact p0015

noncomputable def g_fnresdm
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (.classEq (syn_cres F A) F)) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_fndm A F
  have p0001 :=
    @g_eqimss (syn_cdm F) A
  have p0002 :=
    @g_ssreseq F A
  have p0003 :=
    @g_n_3syl (syn_wfn F A) (.classEq (syn_cdm F) A) (syn_wss (syn_cdm F) A) (.classEq (syn_cres F A) F) p0000 p0001 p0002
  exact p0003

noncomputable def g_fnssresb
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (syn_wb (syn_wfn (syn_cres F B) B) (syn_wss B A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_cres F B) B)))
  have p0001 :=
    @g_fnfun A F
  have p0002 :=
    @g_funres B F
  have p0003 :=
    @g_syl (syn_wfn F A) (syn_wfun F) (syn_wfun (syn_cres F B)) p0001 p0002
  have p0004 :=
    @g_biantrurd (syn_wfn F A) (syn_wfun (syn_cres F B)) (.classEq (syn_cdm (syn_cres F B)) B) p0003
  have p0005 :=
    @g_ssdmres B F
  have p0006 :=
    @g_fndm A F
  have p0007 :=
    @g_sseq2d (syn_wfn F A) (syn_cdm F) A B p0006
  have p0008 :=
    @g_syl5bbr (.classEq (syn_cdm (syn_cres F B)) B) (syn_wss B (syn_cdm F)) (syn_wfn F A) (syn_wss B A) p0005 p0007
  have p0009 :=
    @g_bitr3d (syn_wfn F A) (.classEq (syn_cdm (syn_cres F B)) B) (syn_wa (syn_wfun (syn_cres F B)) (.classEq (syn_cdm (syn_cres F B)) B)) (syn_wss B A) p0004 p0008
  have p0010 :=
    @g_syl5bb (syn_wfn (syn_cres F B) B) (syn_wa (syn_wfun (syn_cres F B)) (.classEq (syn_cdm (syn_cres F B)) B)) (syn_wfn F A) (syn_wss B A) p0000 p0009
  exact p0010

noncomputable def g_fnssres
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wfn (syn_cres F B) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_fnssresb A B F
  have p0001 :=
    @g_biimpar (syn_wfn F A) (syn_wfn (syn_cres F B) B) (syn_wss B A) p0000
  exact p0001

noncomputable def g_fnresin1
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (syn_wfn (syn_cres F (syn_cin A B)) (syn_cin A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_inss1 A B
  have p0001 :=
    @g_fnssres A (syn_cin A B) F
  have p0002 :=
    @g_mpan2 (syn_wfn F A) (syn_wss (syn_cin A B) A) (syn_wfn (syn_cres F (syn_cin A B)) (syn_cin A B)) p0000 p0001
  exact p0002

noncomputable def g_fnres
    (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wfn (syn_cres F A) A) (syn_wral x A (syn_weu y (syn_wbr (.cv x) F (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ F.fv
  have dv_cache_0001 : y ∉ ((Wff.classMem (.cv x) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cres F A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cres F A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cdm (syn_cres F A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ancom (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y))))
  have p0001 :=
    @g_brres (.cv x) (.cv y) F A
  have p0002 :=
    @g_ancom (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) A)
  have p0003 :=
    @g_bitri (syn_wbr (.cv x) (syn_cres F A) (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) A)) (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) p0001 p0002
  have p0004 :=
    @g_mobii (syn_wbr (.cv x) (syn_cres F A) (.cv y)) (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y))) y p0003
  have p0005 :=
    @g_moanimv (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)) y dv_cache_0001
  have p0006 :=
    @g_bitri (syn_wmo y (syn_wbr (.cv x) (syn_cres F A) (.cv y))) (syn_wmo y (syn_wa (.classMem (.cv x) A) (syn_wbr (.cv x) F (.cv y)))) (.imp (.classMem (.cv x) A) (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) p0004 p0005
  have p0007 :=
    @g_albii (syn_wmo y (syn_wbr (.cv x) (syn_cres F A) (.cv y))) (.imp (.classMem (.cv x) A) (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) x p0006
  have p0008 :=
    @g_dffun6 x y (syn_cres F A) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0009 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y))))))
  have p0010 :=
    @g_n_3bitr4i (.all x (syn_wmo y (syn_wbr (.cv x) (syn_cres F A) (.cv y)))) (.all x (.imp (.classMem (.cv x) A) (syn_wmo y (syn_wbr (.cv x) F (.cv y))))) (syn_wfun (syn_cres F A)) (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) p0007 p0008 p0009
  have p0011 :=
    @g_dmres F A
  have p0012 :=
    @g_inss1 A (syn_cdm F)
  have p0013 :=
    @g_eqsstri (syn_cdm (syn_cres F A)) (syn_cin A (syn_cdm F)) A p0011 p0012
  have p0014 :=
    @g_eqss (syn_cdm (syn_cres F A)) A
  have p0015 :=
    @g_mpbiran (.classEq (syn_cdm (syn_cres F A)) A) (syn_wss (syn_cdm (syn_cres F A)) A) (syn_wss A (syn_cdm (syn_cres F A))) p0013 p0014
  have p0016 :=
    @g_dfss3 x A (syn_cdm (syn_cres F A)) dv_cache_0005 dv_cache_0006
  have p0017 :=
    @g_elin2 (.cv x) A (syn_cdm F) (syn_cdm (syn_cres F A)) p0011
  have p0018 :=
    @g_baib (.classMem (.cv x) (syn_cdm (syn_cres F A))) (.classMem (.cv x) A) (.classMem (.cv x) (syn_cdm F)) p0017
  have p0019 :=
    @g_eldm y (.cv x) F dv_cache_0007 dv_cache_0008
  have p0020 :=
    @g_syl6bb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cdm (syn_cres F A))) (.classMem (.cv x) (syn_cdm F)) (syn_wex y (syn_wbr (.cv x) F (.cv y))) p0018 p0019
  have p0021 :=
    @g_ralbiia (.classMem (.cv x) (syn_cdm (syn_cres F A))) (syn_wex y (syn_wbr (.cv x) F (.cv y))) x A p0020
  have p0022 :=
    @g_n_3bitri (.classEq (syn_cdm (syn_cres F A)) A) (syn_wss A (syn_cdm (syn_cres F A))) (syn_wral x A (.classMem (.cv x) (syn_cdm (syn_cres F A)))) (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y)))) p0015 p0016 p0021
  have p0023 :=
    @g_anbi12i (syn_wfun (syn_cres F A)) (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) (.classEq (syn_cdm (syn_cres F A)) A) (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y)))) p0010 p0022
  have p0024 :=
    @g_r19_26 (syn_wex y (syn_wbr (.cv x) F (.cv y))) (syn_wmo y (syn_wbr (.cv x) F (.cv y))) x A
  have p0025 :=
    @g_n_3bitr4i (syn_wa (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y))))) (syn_wa (syn_wral x A (syn_wex y (syn_wbr (.cv x) F (.cv y)))) (syn_wral x A (syn_wmo y (syn_wbr (.cv x) F (.cv y))))) (syn_wa (syn_wfun (syn_cres F A)) (.classEq (syn_cdm (syn_cres F A)) A)) (syn_wral x A (syn_wa (syn_wex y (syn_wbr (.cv x) F (.cv y))) (syn_wmo y (syn_wbr (.cv x) F (.cv y))))) p0000 p0023 p0024
  have p0026 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_cres F A) A)))
  have p0027 :=
    @g_eu5 (syn_wbr (.cv x) F (.cv y)) y
  have p0028 :=
    @g_ralbii (syn_weu y (syn_wbr (.cv x) F (.cv y))) (syn_wa (syn_wex y (syn_wbr (.cv x) F (.cv y))) (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) x A p0027
  have p0029 :=
    @g_n_3bitr4i (syn_wa (syn_wfun (syn_cres F A)) (.classEq (syn_cdm (syn_cres F A)) A)) (syn_wral x A (syn_wa (syn_wex y (syn_wbr (.cv x) F (.cv y))) (syn_wmo y (syn_wbr (.cv x) F (.cv y))))) (syn_wfn (syn_cres F A) A) (syn_wral x A (syn_weu y (syn_wbr (.cv x) F (.cv y)))) p0025 p0026 p0028
  exact p0029

noncomputable def g_fnresi
    (A : Class) :
    Nominal.NPrf (syn_wfn (syn_cres (syn_cid) A) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_funi
  have p0001 :=
    @g_funres A (syn_cid)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_dmresi A
  have p0004 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_cres (syn_cid) A) A)))
  have p0005 :=
    @g_mpbir2an (syn_wfn (syn_cres (syn_cid) A) A) (syn_wfun (syn_cres (syn_cid) A)) (.classEq (syn_cdm (syn_cres (syn_cid) A)) A) p0002 p0003 p0004
  exact p0005

noncomputable def g_fn0
    (F : Class) :
    Nominal.NPrf (syn_wb (syn_wfn F (syn_c0)) (.classEq F (syn_c0))) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    @g_fndm (syn_c0) F
  have p0001 :=
    @g_dmeq0 F
  have p0002 :=
    @g_sylibr (syn_wfn F (syn_c0)) (.classEq (syn_cdm F) (syn_c0)) (.classEq F (syn_c0)) p0000 p0001
  have p0003 :=
    @g_fun0
  have p0004 :=
    @g_dm0
  have p0005 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_c0) (syn_c0))))
  have p0006 :=
    @g_mpbir2an (syn_wfn (syn_c0) (syn_c0)) (syn_wfun (syn_c0)) (.classEq (syn_cdm (syn_c0)) (syn_c0)) p0003 p0004 p0005
  have p0007 :=
    @g_fneq1 (syn_c0) F (syn_c0)
  have p0008 :=
    @g_mpbiri (.classEq F (syn_c0)) (syn_wfn F (syn_c0)) (syn_wfn (syn_c0) (syn_c0)) p0006 p0007
  have p0009 :=
    @g_impbii (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) p0002 p0008
  exact p0009

noncomputable def g_fnopabg
    (ph : Wff) (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) (hyp_fnopabg_1 : Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))) :
    Nominal.NPrf (syn_wb (syn_wral x A (syn_weu y ph)) (syn_wfn F A)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ F.fv
  have dv_cache_0001 : y ∉ ((Wff.classMem (.cv x) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
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
  have p0000 :=
    @g_moanimv (.classMem (.cv x) A) ph y dv_cache_0001
  have p0001 :=
    @g_albii (syn_wmo y (syn_wa (.classMem (.cv x) A) ph)) (.imp (.classMem (.cv x) A) (syn_wmo y ph)) x p0000
  have p0002 :=
    @g_funopab (syn_wa (.classMem (.cv x) A) ph) x y dv_cache_0002
  have p0003 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x A (syn_wmo y ph))))
  have p0004 :=
    @g_n_3bitr4ri (.all x (syn_wmo y (syn_wa (.classMem (.cv x) A) ph))) (.all x (.imp (.classMem (.cv x) A) (syn_wmo y ph))) (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) (syn_wral x A (syn_wmo y ph)) p0001 p0002 p0003
  have p0005 :=
    @g_dmopab3 ph x y A dv_cache_0003 dv_cache_0004 dv_cache_0002
  have p0006 :=
    @g_anbi12i (syn_wral x A (syn_wmo y ph)) (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) (syn_wral x A (syn_wex y ph)) (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A) p0004 p0005
  have p0007 :=
    @g_r19_26 (syn_wmo y ph) (syn_wex y ph) x A
  have p0008 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) A)))
  have p0009 :=
    @g_n_3bitr4i (syn_wa (syn_wral x A (syn_wmo y ph)) (syn_wral x A (syn_wex y ph))) (syn_wa (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A)) (syn_wral x A (syn_wa (syn_wmo y ph) (syn_wex y ph))) (syn_wfn (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) A) p0006 p0007 p0008
  have p0010 :=
    @g_eu5 ph y
  have p0011 :=
    @g_ancom (syn_wex y ph) (syn_wmo y ph)
  have p0012 :=
    @g_bitri (syn_weu y ph) (syn_wa (syn_wex y ph) (syn_wmo y ph)) (syn_wa (syn_wmo y ph) (syn_wex y ph)) p0010 p0011
  have p0013 :=
    @g_ralbii (syn_weu y ph) (syn_wa (syn_wmo y ph) (syn_wex y ph)) x A p0012
  have p0014 :=
    @g_fneq1i A F (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) hyp_fnopabg_1
  have p0015 :=
    @g_n_3bitr4i (syn_wral x A (syn_wa (syn_wmo y ph) (syn_wex y ph))) (syn_wfn (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) A) (syn_wral x A (syn_weu y ph)) (syn_wfn F A) p0009 p0013 p0014
  exact p0015

noncomputable def g_fnopab2g
    (x : Var) (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) (hyp_fnopab2g_1 : Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))) :
    Nominal.NPrf (syn_wb (syn_wral x A (.classMem B (syn_cvv))) (syn_wfn F A)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
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
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_eueq y B dv_cache_0001
  have p0001 :=
    @g_ralbii (.classMem B (syn_cvv)) (syn_weu y (.classEq (.cv y) B)) x A p0000
  have p0002 :=
    @g_fnopabg (.classEq (.cv y) B) x y A F dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_fnopab2g_1
  have p0003 :=
    @g_bitri (syn_wral x A (.classMem B (syn_cvv))) (syn_wral x A (syn_weu y (.classEq (.cv y) B))) (syn_wfn F A) p0001 p0002
  exact p0003

noncomputable def g_fnopab
    (ph : Wff) (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) (hyp_fnopab_1 : Nominal.NPrf (.imp (.classMem (.cv x) A) (syn_weu y ph))) (hyp_fnopab_2 : Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))) :
    Nominal.NPrf (syn_wfn F A) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ F.fv
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
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_rgen (syn_weu y ph) x A hyp_fnopab_1
  have p0001 :=
    @g_fnopabg ph x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fnopab_2
  have p0002 :=
    @g_mpbi (syn_wral x A (syn_weu y ph)) (syn_wfn F A) p0000 p0001
  exact p0002

noncomputable def g_fnopab2
    (x : Var) (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) (hyp_fnopab2_1 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_fnopab2_2 : Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))) :
    Nominal.NPrf (syn_wfn F A) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
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
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_eueq1 y B dv_cache_0001 hyp_fnopab2_1
  have p0001 :=
    @g_a1i (syn_weu y (.classEq (.cv y) B)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_fnopab (.classEq (.cv y) B) x y A F dv_cache_0002 dv_cache_0003 dv_cache_0004 p0001 hyp_fnopab2_2
  exact p0002

noncomputable def g_feq1
    (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (syn_wb (syn_wf F A B) (syn_wf G A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fneq1 A F G
  have p0001 :=
    @g_rneq F G
  have p0002 :=
    @g_sseq1d (.classEq F G) (syn_crn F) (syn_crn G) B p0001
  have p0003 :=
    @g_anbi12d (.classEq F G) (syn_wfn F A) (syn_wfn G A) (syn_wss (syn_crn F) B) (syn_wss (syn_crn G) B) p0000 p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0005 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf G A B)))
  have p0006 :=
    @g_n_3bitr4g (.classEq F G) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) (syn_wa (syn_wfn G A) (syn_wss (syn_crn G) B)) (syn_wf F A B) (syn_wf G A B) p0003 p0004 p0005
  exact p0006

#print axioms g_feq1

end NFChoice.DirectNominalPrf.WPPReplay
