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
import NominalWPPReplayChunk014Compact001Part057

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

noncomputable def g_finleastnn
    (y : Var) (z : Var) (V : Class) (X : Class) (dv_V_y : y ∉ V.fv) (dv_V_z : z ∉ V.fv) (dv_X_y : y ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ V.fv ∪ X.fv
  let t : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_t_not_V : t ∉ V.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_u : z ≠ u :=
    Ne.symm fresh_u_ne_z
  have fresh_u_not_V : u ∉ V.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_X : u ∉ X.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_ne_y : n ≠ y := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_n : y ≠ n :=
    Ne.symm fresh_n_ne_y
  have fresh_n_ne_z : n ≠ z := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_n : z ≠ n :=
    Ne.symm fresh_n_ne_z
  have fresh_n_not_V : n ∉ V.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_X : n ∉ X.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have fresh_t_ne_n : t ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_t : n ≠ t :=
    Ne.symm fresh_t_ne_n
  have fresh_u_ne_n : u ≠ n := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_u : n ≠ u :=
    Ne.symm fresh_u_ne_n
  have dv_cache_0001 : t ∉ (X).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show t ≠ y from (by exact fresh_t_ne_y))
  have dv_cache_0011 : t ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show t ≠ z from (by exact fresh_t_ne_z))
  have dv_cache_0012 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0013 : u ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((syn_cplc (.cv n) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : t ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : t ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0019 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0020 : u ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0021 : n ∉ ((syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_X, fresh_n_not_V, fresh_n_ne_z, fresh_n_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : n ∉ ((syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : t ∉ ((syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_X, fresh_t_ne_z, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : t ∉ ((syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_X, fresh_t_not_V, fresh_t_ne_z, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0001 :=
    @g_simp3 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0002 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wne X (syn_c0)) p0000 p0001
  have p0003 :=
    @g_n0 t X dv_cache_0001
  have p0004 :=
    @g_biimpi (syn_wne X (syn_c0)) (syn_wex t (.classMem (.cv t) X)) p0003
  have p0005 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wne X (syn_c0)) (syn_wex t (.classMem (.cv t) X)) p0002 p0004
  have p0006 :=
    @g_simpr (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0007 :=
    @g_simpl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0008 :=
    @g_simpl (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0009 :=
    @g_simp2 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0010 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wss X (syn_cnnc)) p0008 p0009
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wss X (syn_cnnc)) p0007 p0010
  have p0012 :=
    @g_simpr (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0013 :=
    @g_sseldd (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) X (syn_cnnc) (.cv t) p0011 p0012
  have p0014 :=
    @g_elex (.cv t) (syn_cnnc)
  have p0015 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cnnc)) (.classMem (.cv t) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_lefinrflx (.cv t) (syn_cvv)
  have p0017 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cvv)) (.classMem (syn_copk (.cv t) (.cv t)) (syn_clefin)) p0015 p0016
  have p0018 :=
    @g_simpl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0019 :=
    @g_simpl (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0020 :=
    @g_simp2 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0021 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wss X (syn_cnnc)) p0019 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wss X (syn_cnnc)) p0018 p0021
  have p0023 :=
    @g_simpr (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0024 :=
    @g_sseldd (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) X (syn_cnnc) (.cv t) p0022 p0023
  have p0025 :=
    @g_elex (.cv t) (syn_cnnc)
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cnnc)) (.classMem (.cv t) (syn_cvv)) p0024 p0025
  have p0027 :=
    @g_simpl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0028 :=
    @g_simpl (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0029 :=
    @g_simp2 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0030 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wss X (syn_cnnc)) p0028 p0029
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wss X (syn_cnnc)) p0027 p0030
  have p0032 :=
    @g_simpr (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0033 :=
    @g_sseldd (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) X (syn_cnnc) (.cv t) p0031 p0032
  have p0034 :=
    @g_elex (.cv t) (syn_cnnc)
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cnnc)) (.classMem (.cv t) (syn_cvv)) p0033 p0034
  have p0036 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cvv)) (.classMem (.cv t) (syn_cvv)) p0026 p0035
  have p0037 :=
    @g_kqlefinbr (.cv t) (.cv t) (syn_cvv) (syn_cvv)
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_wa (.classMem (.cv t) (syn_cvv)) (.classMem (.cv t) (syn_cvv))) (syn_wb (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t)) (.classMem (syn_copk (.cv t) (.cv t)) (syn_clefin))) p0036 p0037
  have p0039 :=
    @g_mpbird (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t)) (.classMem (syn_copk (.cv t) (.cv t)) (syn_clefin)) p0017 p0038
  have p0040 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) X) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t)) p0006 p0039
  have p0041 :=
    @g_breq1 (.cv u) (.cv t) (.cv t) (syn_ckqrel (syn_clefin))
  have p0042 :=
    @g_rspcev (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv t)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t)) u (.cv t) X dv_cache_0002 dv_cache_0003 dv_cache_0004 p0041
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_wa (.classMem (.cv t) X) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t))) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv t))) p0040 p0042
  have p0044 :=
    @g_elima u (.cv t) (syn_ckqrel (syn_clefin)) X dv_cache_0002 dv_cache_0005 dv_cache_0003
  have p0045 :=
    @g_a1i (syn_wb (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv t)))) (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) p0044
  have p0046 :=
    @g_mpbird (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv t))) p0043 p0045
  have p0047 :=
    @g_simpl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0048 :=
    @g_vvex
  have p0049 :=
    @g_a1i (.classMem (syn_cvv) (syn_cvv)) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) p0048
  have p0050 :=
    @g_lefinex
  have p0051 :=
    @g_kqrelex (syn_clefin) p0050
  have p0052 :=
    @g_a1i (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) p0051
  have p0053 :=
    @g_simpl (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0054 :=
    @g_simp1 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0055 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.classMem X V) p0053 p0054
  have p0056 :=
    @g_jca (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem X V) p0052 p0055
  have p0057 :=
    @g_imaexg (syn_ckqrel (syn_clefin)) X (syn_cvv) V
  have p0058 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wa (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem X V)) (.classMem (syn_cima (syn_ckqrel (syn_clefin)) X) (syn_cvv)) p0056 p0057
  have p0059 :=
    @g_jca (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cima (syn_ckqrel (syn_clefin)) X) (syn_cvv)) p0049 p0058
  have p0060 :=
    @g_difexg (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X) (syn_cvv) (syn_cvv)
  have p0061 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wa (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cima (syn_ckqrel (syn_clefin)) X) (syn_cvv))) (.classMem (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_cvv)) p0059 p0060
  have p0062 :=
    @g_n_0cex
  have p0063 :=
    @g_a1i (.classMem (syn_c0c) (syn_cvv)) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) p0062
  have p0064 :=
    @g_simpr (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0065 :=
    @g_elima t (syn_c0c) (syn_ckqrel (syn_clefin)) X dv_cache_0006 dv_cache_0007 dv_cache_0001
  have p0066 :=
    @g_biimpi (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) p0065
  have p0067 :=
    @g_simpl (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0068 :=
    @g_simp2 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0069 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wss X (syn_cnnc)) p0067 p0068
  have p0070 :=
    @g_finleastbase y z t X dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0071 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wss X (syn_cnnc)) (.imp (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) p0069 p0070
  have p0072 :=
    @g_syl5 (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0066 p0071
  have p0073 :=
    @g_con3d (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0072
  have p0074 :=
    @g_mpd (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) (.neg (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0064 p0073
  have p0075 :=
    @g_jca (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (syn_c0c) (syn_cvv)) (.neg (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0063 p0074
  have p0076 :=
    @g_eldif (syn_c0c) (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)
  have p0077 :=
    @g_a1i (syn_wb (.classMem (syn_c0c) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.classMem (syn_c0c) (syn_cvv)) (.neg (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X))))) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) p0076
  have p0078 :=
    @g_mpbird (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (syn_c0c) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.classMem (syn_c0c) (syn_cvv)) (.neg (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X)))) p0075 p0077
  have p0079 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0080 :=
    @g_simpr (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))
  have p0081 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0079 p0080
  have p0082 :=
    @g_peano2 (.cv n)
  have p0083 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) p0081 p0082
  have p0084 :=
    @g_elex (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)
  have p0085 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cvv)) p0083 p0084
  have p0086 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0087 :=
    @g_simpl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))
  have p0088 :=
    @g_simpr (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0089 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) p0087 p0088
  have p0090 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) p0086 p0089
  have p0091 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))
  have p0092 :=
    @g_simpr (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0093 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0094 :=
    @g_eldif (.cv n) (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)
  have p0095 :=
    @g_a1i (syn_wb (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.classMem (.cv n) (syn_cvv)) (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))))) (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) p0094
  have p0096 :=
    @g_biimpd (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.classMem (.cv n) (syn_cvv)) (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)))) p0095
  have p0097 :=
    @g_simpr (.classMem (.cv n) (syn_cvv)) (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0098 :=
    @g_syl6 (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.classMem (.cv n) (syn_cvv)) (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0096 p0097
  have p0099 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.imp (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)))) p0093 p0098
  have p0100 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0092 p0099
  have p0101 :=
    @g_elima u (.cv n) (syn_ckqrel (syn_clefin)) X dv_cache_0013 dv_cache_0005 dv_cache_0003
  have p0102 :=
    @g_biimpri (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n))) p0101
  have p0103 :=
    @g_a1i (.imp (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n))) (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) p0102
  have p0104 :=
    @g_con3d (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n))) (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)) p0103
  have p0105 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))) p0100 p0104
  have p0106 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))) p0091 p0105
  have p0107 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))
  have p0108 :=
    @g_elima t (syn_cplc (.cv n) (syn_c1c)) (syn_ckqrel (syn_clefin)) X dv_cache_0014 dv_cache_0007 dv_cache_0001
  have p0109 :=
    @g_biimpi (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c)))) p0108
  have p0110 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c)))) p0107 p0109
  have p0111 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))) (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c)))) p0106 p0110
  have p0112 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))
  have p0113 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0114 :=
    @g_simpr (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))
  have p0115 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0113 p0114
  have p0116 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0117 :=
    @g_simpl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))
  have p0118 :=
    @g_simpl (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0119 :=
    @g_simp2 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0120 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wss X (syn_cnnc)) p0118 p0119
  have p0121 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wss X (syn_cnnc)) p0117 p0120
  have p0122 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (syn_wss X (syn_cnnc)) p0116 p0121
  have p0123 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (.cv n) (syn_cnnc)) (syn_wss X (syn_cnnc)) p0115 p0122
  have p0124 :=
    @g_finleaststep y z u t (.cv n) X dv_cache_0015 dv_cache_0013 dv_cache_0016 dv_cache_0017 dv_cache_0001 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0018 dv_cache_0010 dv_cache_0011 dv_cache_0019 dv_cache_0020 dv_cache_0012
  have p0125 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wss X (syn_cnnc))) (.imp (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c))))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) p0123 p0124
  have p0126 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.imp (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c))))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) p0112 p0125
  have p0127 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c))))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0111 p0126
  have p0128 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0127
  have p0129 :=
    @g_con3d (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0128
  have p0130 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) (.neg (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0090 p0129
  have p0131 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cvv)) (.neg (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0085 p0130
  have p0132 :=
    @g_eldif (syn_cplc (.cv n) (syn_c1c)) (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)
  have p0133 :=
    @g_a1i (syn_wb (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cvv)) (.neg (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))))) (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) p0132
  have p0134 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cvv)) (.neg (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)))) p0131 p0133
  have p0135 :=
    @g_ex (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0134
  have p0136 :=
    @g_ralrimiva (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.imp (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))) n (syn_cnnc) dv_cache_0021 p0135
  have p0137 :=
    @g_n_3jca (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_cvv)) (.classMem (syn_c0c) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))) p0061 p0078 p0136
  have p0138 :=
    @g_peano5 n (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_cvv) dv_cache_0022
  have p0139 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_w3a (.classMem (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_cvv)) (.classMem (syn_c0c) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))))) (syn_wss (syn_cnnc) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0137 p0138
  have p0140 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wss (syn_cnnc) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0047 p0139
  have p0141 :=
    @g_simpl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0142 :=
    @g_simpl (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0143 :=
    @g_simp2 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0144 :=
    @g_syl (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wss X (syn_cnnc)) p0142 p0143
  have p0145 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wss X (syn_cnnc)) p0141 p0144
  have p0146 :=
    @g_simpr (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)
  have p0147 :=
    @g_sseldd (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) X (syn_cnnc) (.cv t) p0145 p0146
  have p0148 :=
    @g_sseldd (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_cnnc) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (.cv t) p0140 p0147
  have p0149 :=
    @g_eldif (.cv t) (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)
  have p0150 :=
    @g_a1i (syn_wb (.classMem (.cv t) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.classMem (.cv t) (syn_cvv)) (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X))))) (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) p0149
  have p0151 :=
    @g_mpbid (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))) (syn_wa (.classMem (.cv t) (syn_cvv)) (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X)))) p0148 p0150
  have p0152 :=
    @g_simpr (.classMem (.cv t) (syn_cvv)) (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0153 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (syn_wa (.classMem (.cv t) (syn_cvv)) (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X)))) (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0151 p0152
  have p0154 :=
    @g_pm2_21d (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0153
  have p0155 :=
    @g_mpd (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X)) (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0046 p0154
  have p0156 :=
    @g_ex (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0155
  have p0157 :=
    @g_exlimdv (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (.classMem (.cv t) X) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) t dv_cache_0023 dv_cache_0024 p0156
  have p0158 :=
    @g_mpd (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) (syn_wex t (.classMem (.cv t) X)) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0005 p0157
  have p0159 :=
    @g_ex (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0158
  have p0160 :=
    @g_pm2_18d (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) p0159
  exact p0160

#print axioms g_finleastnn

end NFChoice.DirectNominalPrf.WPPReplay
