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
import NominalWPPReplayChunk014Compact001Part006

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

noncomputable def g_xnndisj
    (y : Var) (X : Class) (dv_X_y : y ∉ X.fv) :
    Nominal.NPrf (.classEq (syn_cin (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_c0)) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ X.fv
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_disjdif (syn_csn (syn_c0c)) (syn_cnnc)
  have p0001 :=
    @g_xpdisj2 (syn_csn (syn_c0c)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) X X
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0004 :=
    @g_peano1
  have p0005 :=
    @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c)) (syn_cnnc) p0006
  have p0008 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c)))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0003 p0007
  have p0009 :=
    @g_eqcomi (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0008
  have p0010 :=
    @g_xpeq2i (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) X p0009
  have p0011 :=
    @g_ineq2i (syn_cxp X (syn_cdif (syn_cnnc) (syn_csn (syn_c0c)))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cxp X (syn_csn (syn_c0c))) p0010
  have p0012 :=
    @g_eqtr3i (syn_cin (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))))) (syn_c0) (syn_cin (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) p0002 p0011
  have p0013 :=
    @g_eqcomi (syn_c0) (syn_cin (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) p0012
  exact p0013

noncomputable def g_xnnun
    (y : Var) (X : Class) (dv_X_y : y ∉ X.fv) :
    Nominal.NPrf (.classEq (syn_cun (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp X (syn_cnnc))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ X.fv
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_undif2 (syn_csn (syn_c0c)) (syn_cnnc)
  have p0001 :=
    @g_peano1
  have p0002 :=
    @g_snssi (syn_c0c) (syn_cnnc)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_ssequn1 (syn_csn (syn_c0c)) (syn_cnnc)
  have p0005 :=
    @g_mpbi (syn_wss (syn_csn (syn_c0c)) (syn_cnnc)) (.classEq (syn_cun (syn_csn (syn_c0c)) (syn_cnnc)) (syn_cnnc)) p0003 p0004
  have p0006 :=
    @g_eqtri (syn_cun (syn_csn (syn_c0c)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c)))) (syn_cun (syn_csn (syn_c0c)) (syn_cnnc)) (syn_cnnc) p0000 p0005
  have p0007 :=
    @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0008 :=
    @g_peano1
  have p0009 :=
    @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c)) (syn_cnnc) p0010
  have p0012 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c)))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0007 p0011
  have p0013 :=
    @g_eqcomi (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0012
  have p0014 :=
    @g_uneq2i (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_csn (syn_c0c)) p0013
  have p0015 :=
    @g_eqtr3i (syn_cun (syn_csn (syn_c0c)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c)))) (syn_cnnc) (syn_cun (syn_csn (syn_c0c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) p0006 p0014
  have p0016 :=
    @g_eqcomi (syn_cnnc) (syn_cun (syn_csn (syn_c0c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) p0015
  have p0017 :=
    @g_xpeq2i (syn_cun (syn_csn (syn_c0c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cnnc) X p0016
  have p0018 :=
    @g_xpundi X (syn_csn (syn_c0c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
  have p0019 :=
    @g_eqtr3i (syn_cxp X (syn_cun (syn_csn (syn_c0c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp X (syn_cnnc)) (syn_cun (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) p0017 p0018
  have p0020 :=
    @g_eqcomi (syn_cxp X (syn_cnnc)) (syn_cun (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) p0019
  exact p0020

noncomputable def g_sucnnf1o
    (y : Var) (z : Var) (dv_y_z : y ≠ z) :
    Nominal.NPrf (syn_wf1o (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var)
  let w : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have dv_cache_0001 : z ∉ ((syn_cnnc)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_y_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_cplc (.cv w) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cplc (.cv t) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show w ≠ t from (by exact fresh_w_ne_t))
  have dv_cache_0009 : w ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cplc (.cv z) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_y_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show z ≠ y from (by exact Ne.symm dv_y_z))
  have dv_cache_0015 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_y_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((syn_wne (.cv y) (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_y_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqid (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
  have p0001 :=
    @g_peano2 (.cv z)
  have p0002 :=
    @g_peano3 (.cv z)
  have p0003 :=
    @g_jca (.classMem (.cv z) (syn_cnnc)) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cnnc)) (syn_wne (syn_cplc (.cv z) (syn_c1c)) (syn_c0c)) p0001 p0002
  have p0004 :=
    @g_nnnzdf y
  have p0005 :=
    @g_eleq2i (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) (syn_cplc (.cv z) (syn_c1c)) p0004
  have p0006 :=
    @g_eldifsn (syn_cplc (.cv z) (syn_c1c)) (syn_cnnc) (syn_c0c)
  have p0007 :=
    @g_bitri (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c)))) (syn_wa (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cnnc)) (syn_wne (syn_cplc (.cv z) (syn_c1c)) (syn_c0c))) p0005 p0006
  have p0008 :=
    @g_sylibr (.classMem (.cv z) (syn_cnnc)) (syn_wa (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cnnc)) (syn_wne (syn_cplc (.cv z) (syn_c1c)) (syn_c0c))) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) p0003 p0007
  have p0009 :=
    @g_fmpti z (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cplc (.cv z) (syn_c1c)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) dv_cache_0001 dv_cache_0002 p0000 p0008
  have p0010 :=
    @g_addceq1 (.cv z) (.cv w) (syn_c1c)
  have p0011 :=
    @g_eqid (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
  have p0012 :=
    @g_vex w
  have p0013 :=
    @g_n_1cex
  have p0014 :=
    @g_addcex (.cv w) (syn_c1c) p0012 p0013
  have p0015 :=
    @g_fvmpt z (.cv w) (syn_cplc (.cv z) (syn_c1c)) (syn_cplc (.cv w) (syn_c1c)) (syn_cnnc) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) dv_cache_0003 dv_cache_0004 dv_cache_0001 p0010 p0011 p0014
  have p0016 :=
    @g_adantr (.classMem (.cv w) (syn_cnnc)) (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w)) (syn_cplc (.cv w) (syn_c1c))) (.classMem (.cv t) (syn_cnnc)) p0015
  have p0017 :=
    @g_addceq1 (.cv z) (.cv t) (syn_c1c)
  have p0018 :=
    @g_eqid (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
  have p0019 :=
    @g_vex t
  have p0020 :=
    @g_n_1cex
  have p0021 :=
    @g_addcex (.cv t) (syn_c1c) p0019 p0020
  have p0022 :=
    @g_fvmpt z (.cv t) (syn_cplc (.cv z) (syn_c1c)) (syn_cplc (.cv t) (syn_c1c)) (syn_cnnc) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) dv_cache_0005 dv_cache_0006 dv_cache_0001 p0017 p0018 p0021
  have p0023 :=
    @g_adantl (.classMem (.cv t) (syn_cnnc)) (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t)) (syn_cplc (.cv t) (syn_c1c))) (.classMem (.cv w) (syn_cnnc)) p0022
  have p0024 :=
    @g_eqeq12d (syn_wa (.classMem (.cv w) (syn_cnnc)) (.classMem (.cv t) (syn_cnnc))) (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w)) (syn_cplc (.cv w) (syn_c1c)) (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t)) (syn_cplc (.cv t) (syn_c1c)) p0016 p0023
  have p0025 :=
    @g_suc11nnc (.cv w) (.cv t)
  have p0026 :=
    @g_bitrd (syn_wa (.classMem (.cv w) (syn_cnnc)) (.classMem (.cv t) (syn_cnnc))) (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w)) (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t))) (.classEq (syn_cplc (.cv w) (syn_c1c)) (syn_cplc (.cv t) (syn_c1c))) (.classEq (.cv w) (.cv t)) p0024 p0025
  have p0027 :=
    @g_biimpd (syn_wa (.classMem (.cv w) (syn_cnnc)) (.classMem (.cv t) (syn_cnnc))) (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w)) (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t))) (.classEq (.cv w) (.cv t)) p0026
  have p0028 :=
    @g_rgen2 (.imp (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w)) (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t))) (.classEq (.cv w) (.cv t))) w t (syn_cnnc) (syn_cnnc) dv_cache_0007 dv_cache_0008 p0027
  have p0029 :=
    @g_pm3_2i (syn_wf (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_wral w (syn_cnnc) (syn_wral t (syn_cnnc) (.imp (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w)) (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t))) (.classEq (.cv w) (.cv t))))) p0009 p0028
  have p0030 :=
    @g_dff13 w t (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) dv_cache_0009 dv_cache_0007 dv_cache_0010 dv_cache_0011 dv_cache_0008
  have p0031_e01_recanon : Nominal.NPrf (syn_wb (syn_wf1 (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_wa (syn_wf (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_wral w (syn_cnnc) (syn_wral t (syn_cnnc) (.imp (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w)) (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t))) (.classEq (.cv w) (.cv t))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cmpt syn_cnnc syn_cint syn_cplc syn_wrex syn_c1c syn_crab syn_c0c syn_csn syn_c0 syn_cdif syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0030
  have p0031 :=
    @g_mpbir (syn_wf1 (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_wa (syn_wf (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_wral w (syn_cnnc) (syn_wral t (syn_cnnc) (.imp (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w)) (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t))) (.classEq (.cv w) (.cv t)))))) p0029 p0031_e01_recanon
  have p0032 :=
    @g_eqid (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
  have p0033 :=
    @g_rnmpt z y (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) dv_cache_0012 dv_cache_0013 dv_cache_0014 p0032
  have p0034 :=
    @g_olc (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) (.classEq (.cv y) (syn_c0c))
  have p0035 :=
    @g_nnc0suc z (.cv y) dv_cache_0015
  have p0036 :=
    @g_sylibr (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) (syn_wo (.classEq (.cv y) (syn_c0c)) (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))) (.classMem (.cv y) (syn_cnnc)) p0034 p0035
  have p0037 :=
    @g_simpr (.classMem (.cv z) (syn_cnnc)) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))
  have p0038 :=
    @g_peano3 (.cv z)
  have p0039 :=
    @g_adantr (.classMem (.cv z) (syn_cnnc)) (syn_wne (syn_cplc (.cv z) (syn_c1c)) (syn_c0c)) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))) p0038
  have p0040 :=
    @g_eqnetrd (syn_wa (.classMem (.cv z) (syn_cnnc)) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) (.cv y) (syn_cplc (.cv z) (syn_c1c)) (syn_c0c) p0037 p0039
  have p0041 :=
    @g_ex (.classMem (.cv z) (syn_cnnc)) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))) (syn_wne (.cv y) (syn_c0c)) p0040
  have p0042 :=
    @g_rexlimiv (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))) (syn_wne (.cv y) (syn_c0c)) z (syn_cnnc) dv_cache_0016 p0041
  have p0043 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv y) (syn_c0c))))
  have p0044 :=
    @g_sylib (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) (syn_wne (.cv y) (syn_c0c)) (.neg (.classEq (.cv y) (syn_c0c))) p0042 p0043
  have p0045 :=
    @g_jca (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c))) p0036 p0044
  have p0046 :=
    @g_simpr (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))
  have p0047 :=
    @g_pm2_21d (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))) (.classEq (.cv y) (syn_c0c)) (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) p0046
  have p0048 :=
    @g_id (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
  have p0049 :=
    @g_a1i (.imp (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))) p0048
  have p0050 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))
  have p0051 :=
    @g_nnc0suc z (.cv y) dv_cache_0015
  have p0052 :=
    @g_biimpi (.classMem (.cv y) (syn_cnnc)) (syn_wo (.classEq (.cv y) (syn_c0c)) (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))) p0051
  have p0053 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))) (.classMem (.cv y) (syn_cnnc)) (syn_wo (.classEq (.cv y) (syn_c0c)) (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))) p0050 p0052
  have p0054 :=
    @g_mpjaod (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))) (.classEq (.cv y) (syn_c0c)) (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) p0047 p0049 p0053
  have p0055 :=
    @g_impbii (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))) p0045 p0054
  have p0056 :=
    @g_abbii (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))) y p0055
  have p0057 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
  have p0058 :=
    @g_eqtr4i (.cab y (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))) (.cab y (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) p0056 p0057
  have p0059 :=
    @g_eqtri (syn_crn (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (.cab y (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) p0033 p0058
  have p0060 :=
    @g_pm3_2i (syn_wf1 (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (.classEq (syn_crn (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) p0031 p0059
  have p0061 :=
    @g_dff1o5 (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
  have p0062 :=
    @g_mpbir (syn_wf1o (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_wa (syn_wf1 (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (.classEq (syn_crn (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) p0060 p0061
  exact p0062

noncomputable def g_padontoex
    (x : Var) (y : Var) (v : Var) (f : Var) (F : Class) (dv_F_f : f ∉ F.fv) (dv_F_v : v ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_f_v : f ≠ v) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y) (dv_v_x : v ≠ x) (dv_v_y : v ≠ y) (dv_x_y : x ≠ y) (hyp_padontoex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({v} : Finset Var) ∪ ({f} : Finset Var) ∪ F.fv
  have dv_cache_0001 : f ∉ ((syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_f, dv_f_x, dv_f_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_f_x, dv_f_v, dv_f_y, dv_F_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_idex
  have p0001 :=
    @g_snex (syn_c0c)
  have p0002 :=
    @g_resex (syn_cid) (syn_csn (syn_c0c)) p0000 p0001
  have p0003 :=
    @g_pprodexg F (syn_cres (syn_cid) (syn_csn (syn_c0c))) (syn_cvv) (syn_cvv)
  have p0004 :=
    @g_mpan2 (.classMem F (syn_cvv)) (.classMem (syn_cres (syn_cid) (syn_csn (syn_c0c))) (syn_cvv)) (.classMem (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_idex
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_nnnzex y
  have p0008 :=
    @g_xpex (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) p0006 p0007
  have p0009 :=
    @g_resex (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) p0005 p0008
  have p0010 :=
    @g_a1i (.classMem (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cvv)) (.classMem F (syn_cvv)) p0009
  have p0011 :=
    @g_jca (.classMem F (syn_cvv)) (.classMem (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cvv)) (.classMem (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cvv)) p0004 p0010
  have p0012 :=
    @g_unexg (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_syl (.classMem F (syn_cvv)) (syn_wa (.classMem (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cvv)) (.classMem (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cvv))) (.classMem (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_foeq1 (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (.cv f) (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
  have p0015 :=
    @g_spcegv (syn_wfo (.cv f) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) f (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cvv) dv_cache_0001 dv_cache_0002 p0014
  have p0016 :=
    @g_syl (.classMem F (syn_cvv)) (.classMem (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cvv)) (.imp (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) p0013 p0015
  have p0017 :=
    Nominal.mp hyp_padontoex_1 p0016
  exact p0017

noncomputable def g_sucxpinjex
    (x : Var) (y : Var) (z : Var) (v : Var) (g : Var) (dv_g_v : g ≠ v) (dv_g_x : g ≠ x) (dv_g_y : g ≠ y) (dv_g_z : g ≠ z) (dv_v_x : v ≠ x) (dv_v_y : v ≠ y) (dv_v_z : v ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (syn_wf1 (syn_cpprod (syn_cres (syn_cid) (.cv x)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_wex g (syn_wf1 (.cv g) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ({v} : Finset Var) ∪ ({g} : Finset Var)
  have dv_cache_0001 : z ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ ((syn_cpprod (syn_cres (syn_cid) (.cv x)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_g_x, dv_g_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((syn_wf1 (syn_cpprod (syn_cres (syn_cid) (.cv x)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_g_x, dv_g_v, dv_g_y, dv_g_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_idex
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_resex (syn_cid) (.cv x) p0000 p0001
  have p0003 :=
    @g_ssv (syn_cnnc)
  have p0004 :=
    @g_resmpt z (syn_cvv) (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)) dv_cache_0001 dv_cache_0002
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_csucex z
  have p0007 :=
    @g_nncex
  have p0008 :=
    @g_resex (syn_cmpt z (syn_cvv) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) p0006 p0007
  have p0009 :=
    @g_eqeltrri (syn_cres (syn_cmpt z (syn_cvv) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cvv) p0005 p0008
  have p0010 :=
    @g_pprodex (syn_cres (syn_cid) (.cv x)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) p0002 p0009
  have p0011 :=
    @g_f1eq1 (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (.cv g) (syn_cpprod (syn_cres (syn_cid) (.cv x)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
  have p0012 :=
    @g_spcev (syn_wf1 (.cv g) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_wf1 (syn_cpprod (syn_cres (syn_cid) (.cv x)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) g (syn_cpprod (syn_cres (syn_cid) (.cv x)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) dv_cache_0003 dv_cache_0004 p0010 p0011
  exact p0012

noncomputable def g_sucxpinj
    (y : Var) (z : Var) (V : Class) (X : Class) (dv_V_X : Disjoint V.fv X.fv) (dv_V_y : y ∉ V.fv) (dv_V_z : z ∉ V.fv) (dv_X_y : y ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_y_z : y ≠ z) :
    Nominal.NPrf (syn_wf1 (syn_cpprod (syn_cres (syn_cid) X) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp X (syn_cnnc)) (syn_cun (syn_cxp V (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ V.fv ∪ X.fv
  have dv_cache_0001 : y ≠ z := by
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_f1oi X
  have p0001 :=
    @g_sucnnf1o y z dv_cache_0001
  have p0002 :=
    @g_pm3_2i (syn_wf1o (syn_cres (syn_cid) X) X X) (syn_wf1o (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) p0000 p0001
  have p0003 :=
    @g_f1opprod X (syn_cnnc) X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cres (syn_cid) X) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_f1of1 (syn_cxp X (syn_cnnc)) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cpprod (syn_cres (syn_cid) X) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_ssun2 (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cxp V (syn_csn (syn_c0c)))
  have p0008 :=
    @g_pm3_2i (syn_wf1 (syn_cpprod (syn_cres (syn_cid) X) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp X (syn_cnnc)) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_wss (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cun (syn_cxp V (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) p0006 p0007
  have p0009 :=
    @g_f1ss (syn_cxp X (syn_cnnc)) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cun (syn_cxp V (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cpprod (syn_cres (syn_cid) X) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
  have p0010 :=
    Nominal.mp p0008 p0009
  exact p0010

noncomputable def g_wpppadonto
    (y : Var) (F : Class) (V : Class) (X : Class) (dv_F_V : Disjoint F.fv V.fv) (dv_F_X : Disjoint F.fv X.fv) (dv_F_y : y ∉ F.fv) (dv_V_X : Disjoint V.fv X.fv) (dv_V_y : y ∉ V.fv) (dv_X_y : y ∉ X.fv) :
    Nominal.NPrf (.imp (syn_wfo F X V) (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cxp X (syn_cnnc)) (syn_cun (syn_cxp V (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ F.fv ∪ V.fv ∪ X.fv
  have dv_cache_0001 : y ∉ (X).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wfo F X V)
  have p0001 :=
    @g_f1oi (syn_csn (syn_c0c))
  have p0002 :=
    @g_f1ofo (syn_csn (syn_c0c)) (syn_csn (syn_c0c)) (syn_cres (syn_cid) (syn_csn (syn_c0c)))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_jctir (syn_wfo F X V) (syn_wfo F X V) (syn_wfo (syn_cres (syn_cid) (syn_csn (syn_c0c))) (syn_csn (syn_c0c)) (syn_csn (syn_c0c))) p0000 p0003
  have p0005 :=
    @g_fopprod X (syn_csn (syn_c0c)) V (syn_csn (syn_c0c)) F (syn_cres (syn_cid) (syn_csn (syn_c0c)))
  have p0006 :=
    @g_syl (syn_wfo F X V) (syn_wa (syn_wfo F X V) (syn_wfo (syn_cres (syn_cid) (syn_csn (syn_c0c))) (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_wfo (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp V (syn_csn (syn_c0c)))) p0004 p0005
  have p0007 :=
    @g_f1oi (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
  have p0008 :=
    @g_f1ofo (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_jctir (syn_wfo F X V) (syn_wfo (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp V (syn_csn (syn_c0c)))) (syn_wfo (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) p0006 p0009
  have p0011 :=
    @g_xnndisj y X dv_cache_0001
  have p0012 :=
    @g_jctir (syn_wfo F X V) (syn_wa (syn_wfo (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp V (syn_csn (syn_c0c)))) (syn_wfo (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (.classEq (syn_cin (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_c0)) p0010 p0011
  have p0013 :=
    @g_foun (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cxp V (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
  have p0014 :=
    @g_syl (syn_wfo F X V) (syn_wa (syn_wa (syn_wfo (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp V (syn_csn (syn_c0c)))) (syn_wfo (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (.classEq (syn_cin (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_c0))) (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cun (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cun (syn_cxp V (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) p0012 p0013
  have p0015 :=
    @g_xnnun y X dv_cache_0001
  have p0016 :=
    @g_foeq2 (syn_cun (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp X (syn_cnnc)) (syn_cun (syn_cxp V (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_sylib (syn_wfo F X V) (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cun (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cun (syn_cxp V (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cxp X (syn_cnnc)) (syn_cun (syn_cxp V (syn_csn (syn_c0c))) (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) p0014 p0017
  exact p0018

noncomputable def g_f1exco
    (t : Var) (A : Class) (B : Class) (C : Class) (h : Var) (k : Var) (dv_A_h : h ∉ A.fv) (dv_A_k : k ∉ A.fv) (dv_A_t : t ∉ A.fv) (dv_B_h : h ∉ B.fv) (dv_B_k : k ∉ B.fv) (dv_B_t : t ∉ B.fv) (dv_C_h : h ∉ C.fv) (dv_C_k : k ∉ C.fv) (dv_C_t : t ∉ C.fv) (dv_h_k : h ≠ k) (dv_h_t : h ≠ t) (dv_k_t : k ≠ t) :
    Nominal.NPrf (.imp (syn_wa (syn_wex h (syn_wf1 (.cv h) B C)) (syn_wex t (syn_wf1 (.cv t) A B))) (syn_wex k (syn_wf1 (.cv k) A C))) := by
  let proofSupport : Finset Var := ({t} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ ({h} : Finset Var) ∪ ({k} : Finset Var)
  have dv_cache_0001 : t ∉ ((syn_wf1 (.cv h) B C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_t, dv_C_t, (Ne.symm dv_h_t), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((syn_wf1 (.cv t) A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, dv_B_h, dv_h_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((syn_ccom (.cv h) (.cv t))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_h_k), dv_k_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ ((syn_wf1 (syn_ccom (.cv h) (.cv t)) A C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_k, dv_C_k, (Ne.symm dv_h_k), dv_k_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : h ∉ ((syn_wex k (syn_wf1 (.cv k) A C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_h, dv_C_h, dv_h_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_wex k (syn_wf1 (.cv k) A C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_t, dv_C_t, (Ne.symm dv_k_t), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eeanv (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B) h t dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpri (syn_wex h (syn_wex t (syn_wa (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B)))) (syn_wa (syn_wex h (syn_wf1 (.cv h) B C)) (syn_wex t (syn_wf1 (.cv t) A B))) p0000
  have p0002 :=
    @g_f1co A B C (.cv h) (.cv t)
  have p0003 :=
    @g_vex h
  have p0004 :=
    @g_vex t
  have p0005 :=
    @g_coex (.cv h) (.cv t) p0003 p0004
  have p0006 :=
    @g_f1eq1 A C (.cv k) (syn_ccom (.cv h) (.cv t))
  have p0007 :=
    @g_spcev (syn_wf1 (.cv k) A C) (syn_wf1 (syn_ccom (.cv h) (.cv t)) A C) k (syn_ccom (.cv h) (.cv t)) dv_cache_0003 dv_cache_0004 p0005 p0006
  have p0008 :=
    @g_syl (syn_wa (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B)) (syn_wf1 (syn_ccom (.cv h) (.cv t)) A C) (syn_wex k (syn_wf1 (.cv k) A C)) p0002 p0007
  have p0009 :=
    @g_exlimivv (syn_wa (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B)) (syn_wex k (syn_wf1 (.cv k) A C)) h t dv_cache_0005 dv_cache_0006 p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wex h (syn_wf1 (.cv h) B C)) (syn_wex t (syn_wf1 (.cv t) A B))) (syn_wex h (syn_wex t (syn_wa (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B)))) (syn_wex k (syn_wf1 (.cv k) A C)) p0001 p0009
  exact p0010

#print axioms g_f1exco

end NFChoice.DirectNominalPrf.WPPReplay
